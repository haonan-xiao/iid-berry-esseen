"""Checkpointed Path 2 overlay replay. No Slurm submission here.

Only completed per-module records commit reusable results. A worker claims a
queue entry under flock, elaborates it in a unique attempt directory, then
publishes its olean and record. Failed/current chunks are never called proof.
"""
from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import signal
import socket
import subprocess
import tarfile
import tempfile
import time

from path2_nova import (atomic_write_bytes, sha256_file, verify_snapshot,
                        verify_build_sources, parse_imports)

ROOT = Path("/work/stat-grad/xhn/berry_esseen_path2")


def require(test: bool, message: str) -> None:
    if not test:
        raise RuntimeError(message)


def write_json(path: Path, value: dict) -> None:
    atomic_write_bytes(path, (json.dumps(value, sort_keys=True, indent=2) + "\n").encode())


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def stage_literal_inputs(snapshot: Path, project: Path, destination: Path) -> None:
    from verify_path2_subtree_evidence import literal_inputs
    inputs = literal_inputs(snapshot)
    # Validate the entire source set before copying. Existing files must match;
    # a retry never overwrites an input used by an earlier successful record.
    for relative, digest in inputs.items():
        source, target = project / relative, destination / relative
        require(source.is_file() and not source.is_symlink() and sha256_file(source) == digest,
                f"parent literal input mismatch: {relative}")
        if target.exists():
            require(target.is_file() and not target.is_symlink() and sha256_file(target) == digest,
                    f"existing literal input mismatch: {relative}")
    for relative, digest in inputs.items():
        target = destination / relative
        if not target.exists():
            target.parent.mkdir(parents=True, exist_ok=True)
            with (project / relative).open("rb") as source, target.open("xb") as outgoing:
                shutil.copyfileobj(source, outgoing)
            require(sha256_file(target) == digest, "staged literal input changed")
            target.chmod(0o444)


def check_snapshot(snapshot: Path, sid: str) -> dict:
    require(re.fullmatch(r"[0-9a-f]{64}", sid) is not None, "invalid snapshot ID")
    require(sha256_file(snapshot / "source-manifest.tsv") == sid, "overlay manifest mismatch")
    rows = list(csv.reader(io.StringIO((snapshot / "source-manifest.tsv").read_text()), delimiter="\t"))
    names = set()
    for relative, digest, size in rows:
        require(re.fullmatch(r"[A-Za-z0-9_./-]+", relative) is not None and
                not relative.startswith("/") and ".." not in Path(relative).parts,
                "unsafe manifest path")
        require(relative not in names, "duplicate manifest path")
        names.add(relative)
        path = snapshot / relative
        require(path.is_file() and not path.is_symlink() and path.stat().st_size == int(size)
                and sha256_file(path) == digest, f"overlay file mismatch: {relative}")
    actual = {p.relative_to(snapshot).as_posix() for p in snapshot.rglob("*") if p.is_file()}
    require(actual == names | {"source-manifest.tsv"}, "unlisted overlay file")
    plan = read_json(snapshot / "plan.json")
    require(plan["schema"] == "path2-subtree-replay-v1" and plan["proofEvidence"] is False
            and plan["target"] == "879/2000" and plan["maximumWorkers"] == 32,
            "overlay contract mismatch")
    return plan


def install(archive: Path, digest: str, sid: str) -> None:
    require(sha256_file(archive) == digest, "archive hash mismatch")
    target = ROOT / "snapshots" / sid
    require(not target.exists(), "snapshot already installed")
    staging = Path(tempfile.mkdtemp(prefix="subtree-install-", dir=ROOT / "uploads"))
    with tarfile.open(archive, "r:gz") as handle:
        members = handle.getmembers()
        names = [m.name for m in members]
        require(len(names) == len(set(names)), "duplicate archive member")
        require(sum(m.size for m in members) < 100_000_000, "oversized source archive")
        for m in members:
            require(m.isfile() and not m.name.startswith("/") and
                    ".." not in Path(m.name).parts and "\\" not in m.name,
                    "unsafe archive member")
            destination = staging / m.name
            destination.parent.mkdir(parents=True, exist_ok=True)
            with handle.extractfile(m) as incoming, destination.open("xb") as outgoing:
                shutil.copyfileobj(incoming, outgoing)
    check_snapshot(staging, sid)
    # On Nova's filesystem rename of a directory across parents needs its
    # owner-write bit. Freeze permissions only after the rename.
    staging.rename(target)
    for path in target.rglob("*"):
        path.chmod(0o555 if path.is_dir() else 0o444)
    target.chmod(0o555)
    print(json.dumps(dict(installedSnapshot=sid, proofEvidence=False)))


class Replay:
    def __init__(self, sid: str, *, verify: bool = True):
        self.sid = sid
        self.snapshot = ROOT / "snapshots" / sid
        self.plan = check_snapshot(self.snapshot, sid) if verify else read_json(self.snapshot / "plan.json")
        self.parent = ROOT / "snapshots" / self.plan["parentSnapshot"]
        self.parent_build = ROOT / "builds" / self.plan["parentSnapshot"]
        self.project = self.parent_build / "workspace/projects/berry-esseen/lean"
        self.parent_sources = self.project / "Path2"
        self.build = ROOT / "builds" / sid
        self.sources = self.build / "Path2"
        self.records = self.build / "records"
        self.dependency_lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
            cwd=self.project, env=dict(os.environ, LEAN_PATH=""), text=True).strip().rstrip(":")
        self.env = dict(os.environ, LEAN_PATH=f"{self.sources}:{self.build / 'external'}:{self.parent_sources}:{self.dependency_lean_path}")
        self.source_hashes = {m: sha256_file(self.snapshot / "sources" / f"{m}.lean")
                              for m in self.plan["moduleOrder"]}
        self.modules = set(self.plan["moduleOrder"])

    def checked_record(self, module: str) -> dict | None:
        path = self.records / f"{module}.json"
        if not path.exists():
            return None
        value = read_json(path)
        require(value["module"] == module and value["snapshotId"] == self.sid
                and value["sourceSha256"] == self.source_hashes[module]
                and value["exitCode"] == 0 and value["proofEvidence"] is False,
                f"bad checkpoint identity: {module}")
        require(sha256_file(self.sources / f"{module}.olean") == value["oleanSha256"],
                f"bad checkpoint olean: {module}")
        return value

    def imports_ready(self, module: str) -> bool:
        return all((self.records / f"{m}.json").is_file()
                   for m in self.plan["imports"][module] if m in self.modules)

    def compile(self, module: str, role: str, *, timeout: int = 7200) -> bool:
        import fcntl
        with (self.build / "locks" / (module + ".lock")).open("a") as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                return False
            if self.checked_record(module) is not None:
                return True
            if not self.imports_ready(module):
                return False
            dependencies = {m: self.checked_record(m)["oleanSha256"]
                            for m in self.plan["imports"][module] if m in self.modules}
            require(sha256_file(self.sources / f"{module}.lean") == self.source_hashes[module],
                    f"changed build source: {module}")
            attempt = Path(tempfile.mkdtemp(prefix=module + "-", dir=self.build / "attempts"))
            output = attempt / f"{module}.olean"
            log, timing = attempt / "lean.log", attempt / "time.txt"
            command = ["/usr/bin/time", "-v", "-o", str(timing), "lake", "env", "env",
                       "LEAN_PATH="+self.env["LEAN_PATH"], "lean",
                       "-j1", "--tstack=32768", "-R", str(self.sources),
                       "-o", str(output), str(self.sources / f"{module}.lean")]
            start = time.time()
            code = None
            with log.open("w") as stream:
                process = subprocess.Popen(command, cwd=self.project, env=self.env,
                    stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    code = process.wait(timeout=timeout)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                    code = 124
            result = dict(module=module, snapshotId=self.sid, role=role,
                proofEvidence=False, sourceSha256=self.source_hashes[module], exitCode=code,
                imports=dependencies, hostname=socket.gethostname(),
                slurmJobId=os.environ.get("SLURM_JOB_ID"),
                slurmArrayJobId=os.environ.get("SLURM_ARRAY_JOB_ID"),
                slurmArrayTaskId=os.environ.get("SLURM_ARRAY_TASK_ID"),
                startedAtUnix=start, elapsedSeconds=time.time()-start, command=command,
                dependencyLeanPath=self.dependency_lean_path,
                logPath=str(log.relative_to(self.build)), logSha256=sha256_file(log),
                timePath=str(timing.relative_to(self.build)),
                timeSha256=sha256_file(timing) if timing.exists() else None)
            if code == 0 and output.is_file():
                result["oleanSha256"] = sha256_file(output)
                output.replace(self.sources / output.name)
                write_json(self.records / f"{module}.json", result)
                print(json.dumps(dict(checked=module, seconds=result["elapsedSeconds"], proofEvidence=False)), flush=True)
                return True
            write_json(attempt / "FAILED.json", result)
            print(json.dumps(dict(failed=module, exitCode=code, attempt=str(attempt))), flush=True)
            return False

    def reuse(self, entry: dict, run_ids: list[str]) -> None:
        module, index = entry["module"], entry["index"]
        require(self.source_hashes[module] == sha256_file(self.parent_sources / f"{module}.lean"),
                f"reuse source differs: {module}")
        candidates = [ROOT / "runs" / r / f"{index:02}-{module}.result.json" for r in run_ids]
        successful = []
        for path in candidates:
            if not path.is_file():
                continue
            data = read_json(path)
            if data.get("exitCode") != 0:
                continue
            require(data.get("snapshotId") == self.plan["parentSnapshot"] and
                    data.get("taskIndex") == index and data.get("finalTaskCount") == 18 and
                    data.get("sourceSha256", "").lower() == self.source_hashes[module] and
                    data.get("baseReadySha256", "").lower() == self.plan["parentBaseReadySha256"] and
                    data.get("task", {}).get("theorem") == entry["theorem"], "legacy result identity mismatch")
            for kind in ["olean", "log", "time"]:
                artifact = Path(data[kind+"Path"])
                require(artifact.resolve().is_relative_to(ROOT) and artifact.is_file() and
                        sha256_file(artifact) == data[kind+"Sha256"].lower(), "legacy artifact mismatch")
            require(str(data["slurmArrayTaskId"]) == str(index) and
                    str(data["slurmArrayJobId"]).isdigit(), "legacy array identity mismatch")
            # Slurm can give the last array task the parent's raw JobID;
            # querying that raw ID would return every task, not this root.
            effective_job = f'{data["slurmArrayJobId"]}_{index}'
            state = subprocess.check_output(["sacct", "-X", "-j", effective_job,
                "--noheader", "--parsable2", "--format=State,ExitCode"], text=True).strip()
            require(state == "COMPLETED|0:0", f"legacy Slurm job not successful: {state}")
            successful.append((path, data, state))
        require(len(successful) == 1, f"expected one successful reuse candidate: {module}")
        path, data, state = successful[0]
        reuse_dir = self.build / "reused" / module
        reuse_dir.mkdir(parents=True)
        shutil.copyfile(path, reuse_dir / "result.json")
        for kind in ["log", "time"]:
            shutil.copyfile(data[kind+"Path"], reuse_dir / (kind + ".txt"))
        shutil.copyfile(data["oleanPath"], self.sources / f"{module}.olean")
        write_json(self.records / f"{module}.json", dict(module=module, snapshotId=self.sid,
            sourceSha256=self.source_hashes[module], exitCode=0, proofEvidence=False,
            oleanSha256=data["oleanSha256"].lower(), role="reused-parent-native",
            parentResultSha256=sha256_file(path), parentResultPath=str(path),
            parentSlurmState=state, parentEffectiveJobId=f'{data["slurmArrayJobId"]}_{index}',
            parentSnapshot=self.plan["parentSnapshot"]))

    def prepare_external(self) -> None:
        """Freeze existing dependency oleans; elaborate only missing modules.

        All BerryEsseen source bytes are bound to the checked parent manifest.
        No parent build artifact is modified and no old certificate is rerun.
        """
        external = self.build/"external"
        external.mkdir()
        records, visiting = {}, set()
        def visit(module: str) -> None:
            if not module.startswith("BerryEsseen.") or module in records:
                return
            require(module not in visiting, "external import cycle")
            visiting.add(module)
            relative = Path(*module.split("."))
            source = (self.project/relative).with_suffix(".lean")
            dependencies = parse_imports(source)
            for dependency in dependencies:
                visit(dependency)
            destination = (external/relative).with_suffix(".lean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
            output = destination.with_suffix(".olean")
            old = (self.project/".lake/build/lib/lean"/relative).with_suffix(".olean")
            entry = dict(sourceSha256=sha256_file(source), imports=dependencies, proofEvidence=False)
            if old.is_file():
                shutil.copyfile(old, output)
                entry.update(role="reused-parent-dependency", parentOleanPath=str(old))
            else:
                attempt = Path(tempfile.mkdtemp(prefix="external-"+module+"-", dir=self.build/"attempts"))
                log, timing = attempt/"lean.log", attempt/"time.txt"
                command = ["/usr/bin/time", "-v", "-o", str(timing), "lake", "env", "env",
                           "LEAN_PATH="+self.env["LEAN_PATH"], "lean",
                           "-j1", "--tstack=32768", "-R", str(external), "-o", str(output), str(destination)]
                with log.open("w") as stream:
                    result = subprocess.run(command, cwd=self.project, env=self.env,
                                            stdout=stream, stderr=subprocess.STDOUT, timeout=600)
                require(result.returncode == 0 and output.is_file(), f"external dependency failed: {module}; {log}")
                entry.update(role="new-parent-dependency", command=command, exitCode=0,
                    logPath=str(log.relative_to(self.build)), logSha256=sha256_file(log),
                    timePath=str(timing.relative_to(self.build)), timeSha256=sha256_file(timing))
            entry["oleanSha256"] = sha256_file(output)
            records[module] = entry
            visiting.remove(module)
        for module in self.plan["externalImports"]:
            visit(module)
        write_json(self.build/"EXTERNAL_READY.json", dict(snapshotId=self.sid, proofEvidence=False,
            parentSnapshot=self.plan["parentSnapshot"], modules=records))

    def prepare(self, run_ids: list[str]) -> None:
        require(not self.build.exists(), "overlay build already exists")
        verify_snapshot(self.parent, self.plan["parentSnapshot"])
        verify_build_sources(self.parent, self.parent_build / "workspace")
        ready = self.parent_build / "BASE_READY.json"
        require(sha256_file(ready) == self.plan["parentBaseReadySha256"], "parent base identity changed")
        self.build.mkdir()
        shutil.copytree(self.snapshot / "sources", self.sources)
        # copytree preserves the immutable source directory mode; the build
        # directory must admit generated oleans, while .lean files stay read-only.
        self.sources.chmod(0o755)
        for name in ["records", "locks", "attempts", "reused"]:
            (self.build / name).mkdir()
        self.prepare_external()
        for entry in self.plan["reusedRoots"]:
            self.reuse(entry, run_ids)
        native = set(self.plan["nativeTheorems"])
        for module in self.plan["moduleOrder"]:
            if module in native or not self.imports_ready(module):
                continue
            parent_source = self.parent_sources / f"{module}.lean"
            parent_olean = self.parent_sources / f"{module}.olean"
            if (parent_source.is_file() and parent_olean.is_file() and
                    sha256_file(parent_source) == self.source_hashes[module]):
                shutil.copyfile(parent_olean, self.sources / parent_olean.name)
                write_json(self.records / f"{module}.json", dict(module=module, snapshotId=self.sid,
                    sourceSha256=self.source_hashes[module], exitCode=0, proofEvidence=False,
                    oleanSha256=sha256_file(parent_olean), role="reused-parent-analytic",
                    parentSnapshot=self.plan["parentSnapshot"], parentOleanPath=str(parent_olean)))
            else:
                require(self.compile(module, "new-symbolic"), f"symbolic gate failed: {module}")
        for task in self.plan["numericalTasks"]:
            require(self.imports_ready(task["module"]), "numerical dependencies incomplete")
        ready_data = dict(schema="path2-subtree-base-v1", snapshotId=self.sid,
            parentSnapshot=self.plan["parentSnapshot"], parentBaseReadySha256=sha256_file(ready),
            externalReadySha256=sha256_file(self.build/"EXTERNAL_READY.json"),
            dependencyLeanPath=self.dependency_lean_path,
            leanVersion=subprocess.check_output(["lean", "--version"], cwd=self.project,
                                                env=self.env, text=True).strip(),
            recordHashes={p.stem: sha256_file(p) for p in sorted(self.records.glob("*.json"))},
            proofEvidence=False)
        write_json(self.build / "BASE_READY.json", ready_data)
        ordered = sorted(self.plan["numericalTasks"], key=lambda e: (-e["leaves"]*(1.2 if e["n"] < 11 else 1), e["index"]))
        write_json(self.build / "queue.json", dict(modules=[e["module"] for e in ordered], next=0))
        print(json.dumps(dict(baseReady=True, snapshotId=self.sid, proofEvidence=False)))

    def verify_ready(self) -> None:
        base = read_json(self.build / "BASE_READY.json")
        require(base["snapshotId"] == self.sid, "base snapshot mismatch")
        require(sha256_file(self.build/"EXTERNAL_READY.json") == base["externalReadySha256"],
                "external dependency receipt changed")
        for module, record in read_json(self.build/"EXTERNAL_READY.json")["modules"].items():
            path = self.build/"external"/Path(*module.split("."))
            require(sha256_file(path.with_suffix(".olean")) == record["oleanSha256"]
                    and sha256_file(path.with_suffix(".lean")) == record["sourceSha256"],
                    "external dependency changed")
        for module, digest in base["recordHashes"].items():
            require(sha256_file(self.records / f"{module}.json") == digest, "base record changed")
            self.checked_record(module)

    def assemble_n(self, n: int) -> None:
        assembly = next(e for e in self.plan["assemblies"] if e["n"] == n)
        if self.compile(assembly["module"], "per-n-composition"):
            batch = next(m for m in self.plan["batchModules"]
                         if assembly["module"] in self.plan["imports"][m])
            self.compile(batch, "finite-batch-composition")

    def pilot(self) -> None:
        self.verify_ready()
        tasks = [e for e in self.plan["numericalTasks"] if e["n"] == 1]
        require(len(tasks) >= 2, "pilot must exercise multiple shards")
        for task in tasks:
            require(self.compile(task["module"], "numerical-shard"), "pilot shard failed")
        self.assemble_n(1)
        module = next(e["module"] for e in self.plan["assemblies"] if e["n"] == 1)
        require(self.checked_record(module) is not None, "pilot composition failed")
        before = {e["module"]: sha256_file(self.records / (e["module"]+".json")) for e in tasks}
        attempts = len(list((self.build / "attempts").iterdir()))
        for task in tasks:
            require(self.compile(task["module"], "numerical-shard"), "checkpoint reuse failed")
        require(len(list((self.build / "attempts").iterdir())) == attempts and
                before == {m: sha256_file(self.records / (m+".json")) for m in before},
                "resume repeated a completed computation")
        write_json(self.build / "PILOT_READY.json", dict(snapshotId=self.sid,
            proofEvidence=False, completedN=1, shardCount=len(tasks),
            assemblyRecordSha256=sha256_file(self.records / (module+".json")),
            resumeStartedNoNewAttempt=True))

    def claim(self) -> str | None:
        import fcntl
        with (self.build / "queue.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            path = self.build / "queue.json"
            queue = read_json(path)
            if queue["next"] >= len(queue["modules"]):
                return None
            module = queue["modules"][queue["next"]]
            queue["next"] += 1
            # The mutable queue is scheduling state, never evidence.
            temp = self.build / "queue.next.json"
            with temp.open("w") as stream:
                json.dump(queue, stream)
                stream.flush()
                os.fsync(stream.fileno())
            temp.replace(path)
            return module

    def worker(self) -> None:
        self.verify_ready()
        require((self.build / "PILOT_READY.json").is_file(), "pilot gate missing")
        cutover = read_json(self.build / "CUTOVER_READY.json")
        require(cutover["snapshotId"] == self.sid and cutover["maximumWorkers"] == 32,
                "cutover authorization identity mismatch")
        by_module = {e["module"]: e for e in self.plan["numericalTasks"]}
        while (module := self.claim()) is not None:
            if self.compile(module, "numerical-shard"):
                self.assemble_n(by_module[module]["n"])

    def cutover(self) -> None:
        self.verify_ready()
        pilot = read_json(self.build / "PILOT_READY.json")
        require(pilot["snapshotId"] == self.sid and pilot["resumeStartedNoNewAttempt"] is True,
                "pilot gate incomplete")
        from verify_path2_subtree_evidence import verify_evidence
        verify_evidence(self.snapshot, self.build)
        from verify_path2_final_evidence import EXPECTED_TASK_PAIRS
        for i in self.plan["replacedIndices"]:
            for run in ["final-certificates-12192895", "final-certificates-12215967"]:
                result = ROOT/"runs"/run/f"{i:02}-{EXPECTED_TASK_PAIRS[i][0]}.result.json"
                require(not result.is_file() or read_json(result).get("exitCode") != 0,
                        "a legacy root just completed: regenerate the overlay to reuse it before cancellation")
        jobs = [f"{12215967 if i in (0,2,3) else 12192895}_{i}" for i in self.plan["replacedIndices"]]
        output = subprocess.check_output(["squeue", "-h", "-u", "xhn", "-o", "%i|%j"], text=True)
        active = [line.split("|")[0] for line in output.splitlines()
                  if line.split("|")[0] in jobs]
        require(all(line.split("|")[1] == "be-p2-final" for line in output.splitlines()
                    if line.split("|")[0] in active), "unexpected old job name")
        for job in active:
            detail = subprocess.check_output(["scontrol", "show", "job", job, "-o"], text=True)
            require(self.plan["parentSnapshot"] in detail and "berry_esseen_path2" in detail,
                    "old job does not bind the expected parent snapshot")
        intent = dict(snapshotId=self.sid, maximumWorkers=32, proposedOldJobs=jobs,
            activeOldJobs=active, proofEvidence=False,
            authorization="User approved stop only unfinished covered old jobs after new-scheme gate")
        intent_path = self.build/"CUTOVER_INTENT.json"
        if intent_path.exists():
            previous = read_json(intent_path)
            require(previous["snapshotId"] == self.sid and previous["proposedOldJobs"] == jobs,
                    "cutover intent mismatch")
        else:
            write_json(intent_path, intent)
        if active:
            subprocess.run(["scancel", *active], check=True)
        for _ in range(45):
            output = subprocess.check_output(["squeue", "-h", "-u", "xhn", "-o", "%i"], text=True)
            if not (set(output.splitlines()) & set(jobs)):
                break
            time.sleep(1)
        require(not (set(output.splitlines()) & set(jobs)), "old jobs have not stopped; do not start workers")
        write_json(self.build/"CUTOVER_READY.json", dict(intent, finishedAtUnix=time.time(),
            pilotSha256=sha256_file(self.build/"PILOT_READY.json"),
            baseReadySha256=sha256_file(self.build/"BASE_READY.json")))
        print(json.dumps(dict(cutoverReady=True, stoppedJobs=active, proofEvidence=False)))

    def resume_queue(self, retry_modules: list[str]) -> None:
        self.verify_ready()
        active = subprocess.check_output(["squeue", "-h", "-u", "xhn", "-n", "be-p2-subtrees"], text=True)
        require(not active.strip(), "do not reset a queue while subtree jobs are active")
        tasks = {e["module"]: e for e in self.plan["numericalTasks"]}
        require(set(retry_modules) <= set(tasks), "unknown retry module")
        failed = {read_json(p)["module"] for p in (self.build/"attempts").glob("*/FAILED.json")}
        missing = [m for m in tasks if self.checked_record(m) is None]
        require(not (set(missing) & failed) - set(retry_modules),
                "failed modules require explicit reviewed --retry-modules; missing-only resume cannot retry failures")
        missing.sort(key=lambda m: (-tasks[m]["leaves"]*(1.2 if tasks[m]["n"] < 11 else 1), tasks[m]["index"]))
        path = self.build/"queue.json"
        history = self.build/("queue-history-"+sha256_file(path)+".json")
        if not history.exists():
            shutil.copyfile(path, history)
        temp = self.build/"queue.next.json"
        with temp.open("w") as stream:
            json.dump(dict(modules=missing, next=0), stream)
            stream.flush()
            os.fsync(stream.fileno())
        temp.replace(path)
        print(json.dumps(dict(remainingModules=len(missing), preservedModules=len(tasks)-len(missing), proofEvidence=False)))

    def finalize(self) -> None:
        from verify_path2_subtree_evidence import execution_repair_paths
        repair_files = execution_repair_paths(self.build)
        require(Path(__file__).resolve() in [p.resolve() for p in repair_files],
                "finalizer must execute the pinned repair")
        self.verify_ready()
        for e in self.plan["numericalTasks"]:
            require(self.checked_record(e["module"]) is not None, "numerical shard missing")
        for e in self.plan["assemblies"]:
            require(self.compile(e["module"], "per-n-composition"), "per-n composition failed")
        for module in self.plan["moduleOrder"]:
            if self.checked_record(module) is None:
                role = "topology-native" if module == self.plan["topology"]["module"] else "final-assembly"
                require(self.compile(module, role), f"final assembly failed: {module}")
        # Fresh analytic elaboration is kept separate from the checkpoint
        # environment: imported witness identities are never overwritten.
        fresh = Replay(self.sid)
        fresh.sources = self.build / "fresh" / "Path2"
        fresh.records = self.build / "fresh" / "records"
        fresh.sources.mkdir(parents=True, exist_ok=True)
        fresh.records.mkdir(exist_ok=True)
        stage_literal_inputs(self.snapshot, self.project, self.build / "fresh")
        fresh.env = dict(self.env, LEAN_PATH=f"{fresh.sources}:{self.sources}:{self.build / 'external'}:{self.parent_sources}:{self.dependency_lean_path}")
        for module in self.plan["moduleOrder"]:
            destination = fresh.sources / f"{module}.lean"
            if destination.exists():
                require(sha256_file(destination) == self.source_hashes[module], "changed fresh source")
            else:
                shutil.copyfile(self.sources / f"{module}.lean", destination)
            if module in self.plan["nativeTheorems"]:
                if not (fresh.records / f"{module}.json").exists():
                    shutil.copyfile(self.sources / f"{module}.olean", fresh.sources / f"{module}.olean")
                    shutil.copyfile(self.records / f"{module}.json", fresh.records / f"{module}.json")
            else:
                require(fresh.compile(module, "fresh-final-analytic"), f"fresh elaboration failed: {module}")
        from verify_path2_subtree_evidence import verify_evidence, artifact_paths
        receipt = verify_evidence(self.snapshot, self.build, final=True)
        paths = artifact_paths(self.snapshot, self.build)
        manifest = "".join(f"{p.relative_to(ROOT).as_posix()}\t{sha256_file(p)}\t{p.stat().st_size}\n" for p in paths).encode()
        final = dict(receipt, evidenceManifestSha256=hashlib.sha256(manifest).hexdigest(),
                     artifactCount=len(paths))
        ready_bytes = (json.dumps(final, sort_keys=True, indent=2)+"\n").encode()
        # The archive is built in an unpublished attempt; FINAL_READY is the
        # last commit marker. Failed packaging never removes accepted results.
        staging = Path(tempfile.mkdtemp(prefix="evidence-", dir=self.build/"attempts"))
        archive = staging/"subtree-final-evidence.tar.gz"
        with archive.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as zipped, tarfile.open(fileobj=zipped, mode="w") as handle:
            for path in paths:
                handle.add(path, arcname=path.relative_to(ROOT).as_posix(), recursive=False)
            for name, content in [("evidence-manifest.tsv",manifest), ("FINAL_READY.json",ready_bytes)]:
                info = tarfile.TarInfo(f"builds/{self.sid}/{name}")
                info.size, info.mode = len(content), 0o444
                handle.addfile(info, io.BytesIO(content))
        destination = self.build/archive.name
        archive_sha = sha256_file(archive)
        if destination.exists():
            require(sha256_file(destination) == archive_sha, "previous evidence archive differs")
        else:
            archive.rename(destination)
        for path, content in [(self.build/"subtree-final-evidence.tar.gz.sha256",
                               (archive_sha+"  subtree-final-evidence.tar.gz\n").encode()),
                              (self.build/"evidence-manifest.tsv",manifest),
                              (self.build/"FINAL_READY.json",ready_bytes)]:
            if path.exists():
                require(path.read_bytes() == content, "existing final receipt differs")
            else:
                atomic_write_bytes(path,content)
        print(json.dumps(dict(finalReady=True, snapshotId=self.sid, proofEvidence=False)))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["install", "prepare", "pilot", "worker", "cutover", "resume-queue", "finalize"])
    parser.add_argument("snapshot")
    parser.add_argument("--archive", type=Path)
    parser.add_argument("--archive-sha256")
    parser.add_argument("--parent-runs", default="final-certificates-12192895,final-certificates-12215967")
    parser.add_argument("--retry-modules", default="")
    args = parser.parse_args()
    if args.mode == "install":
        install(args.archive, args.archive_sha256, args.snapshot)
        return
    if args.mode not in ("cutover", "resume-queue"):
        require(re.fullmatch(r"nova\d+-\d+", socket.gethostname()) is not None,
                "Lean replay must run on a Nova compute node")
    replay = Replay(args.snapshot)
    if args.mode == "prepare":
        replay.prepare(args.parent_runs.split(","))
    elif args.mode == "resume-queue":
        replay.resume_queue([m for m in args.retry_modules.split(",") if m])
    else:
        getattr(replay, args.mode)()


if __name__ == "__main__":
    main()
