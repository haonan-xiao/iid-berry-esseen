"""Audit the execution archive for the 0.4395 Berry--Esseen bound.

Check source identities, successful compilation records, dependencies and
the final axiom inventory. This inspects recorded evidence; it does not
repeat the Lean numerical computations.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import tarfile

from verify_manifest import (EXPECTED_TASK_PAIRS, FINAL_ROOTS,
    scan_source, strip_lean_comments_and_strings)

PARENT = "76120b0d7d0b926c9c92f1e606ab9da45dd18ac62f9cb2a560b2299c8f785534"
BASE_READY = "18011d1a666ef1629f313f9aaf9e5efd45d58db1b15baa7623faade4b07195dc"
PREFIX = "projects/berry-esseen/lean/Path2/"
STANDARDS = {"propext", "Classical.choice", "Quot.sound"}
SUPPORT = {
    "Path2Post044FiniteSubtreePrototype": "b24af270ed771dd956a983e59ea658a6951b2978289792ab7ee77673ba739a77",
    "Path2Post044FiniteFastEvaluator": "3468aa4041755caa7d5c1c8a4d139baa460d7692f2761b004217df77f9886b56",
    "Path2Post044FiniteFastCover": "8ae2c3ec24265a0ebca4bddf55543e7e0981442ae2cd93f3248f47c5e7d873b4",
}


def need(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def literal_inputs(snapshot: Path) -> dict[str, str]:
    """Relative data inputs, not imported axioms; identity comes from the parent."""
    parent = {p: h for p, h, _ in csv.reader(io.StringIO(
        (snapshot / "parent-source-manifest.tsv").read_text()), delimiter="\t")}
    inputs = {}
    for path in sorted((snapshot / "sources").glob("*.lean")):
        source = path.read_text(encoding="utf-8")
        code = strip_lean_comments_and_strings(source, path.stem)
        # This fixed closure uses ordinary literal paths only. Reject a new
        # spelling rather than silently omitting a file from the evidence.
        references = re.findall(r'\binclude_str\s+"([^"\n]+)"', source)
        need(len(references) == len(re.findall(r"\binclude_str\b", code)),
             f"unsupported include_str syntax: {path.stem}")
        for reference in references:
            need(re.fullmatch(r"\.\./BerryEsseen/[A-Za-z0-9_]+\.lean", reference) is not None,
                 "unsafe literal input path")
            relative = reference[3:]
            key = "projects/berry-esseen/lean/" + relative
            need(key in parent, "literal input absent from parent manifest")
            inputs[relative] = parent[key]
    return inputs


def audit_literal_inputs(snapshot: Path, build: Path) -> dict[str, str]:
    inputs = literal_inputs(snapshot)
    for relative, sha in inputs.items():
        path = build / "fresh" / relative
        need(path.is_file() and not path.is_symlink() and digest(path) == sha,
             f"literal input identity mismatch: {relative}")
    return inputs


def execution_repair_paths(build: Path) -> list[Path]:
    """Audit operational code separately; never mutate the proof snapshot."""
    receipt_path = build / "EXECUTION_REPAIR.json"
    receipt = load(receipt_path)
    repair_id = receipt["repairId"]
    need(re.fullmatch(r"[0-9a-f]{64}", repair_id) is not None and
         receipt["snapshotId"] == build.name and receipt["proofEvidence"] is False,
         "execution repair identity mismatch")
    directory = build / "execution-repair" / repair_id
    manifest = directory / "source-manifest.tsv"
    need(digest(manifest) == repair_id, "execution repair manifest mismatch")
    rows = list(csv.reader(io.StringIO(manifest.read_text()), delimiter="\t"))
    expected = {"path2_subtree_replay.py", "verify_path2_subtree_evidence.py",
                "verify_path2_final_evidence.py", "path2_nova.py", "path2_subtree_replay.sbatch"}
    need(len(rows) == len(expected) and {row[0] for row in rows} == expected,
         "unexpected execution repair file set")
    for name, sha, size in rows:
        path = directory / name
        need(path.is_file() and not path.is_symlink() and path.stat().st_size == int(size)
             and digest(path) == sha, "execution repair file mismatch")
    need({p.name for p in directory.iterdir()} == expected | {manifest.name},
         "unlisted execution repair file")
    return [receipt_path, manifest] + [directory / name for name in sorted(expected)]


def preflight(snapshot: Path) -> tuple[dict, dict[str, str]]:
    sid = digest(snapshot / "source-manifest.tsv")
    entries = list(csv.reader(io.StringIO((snapshot / "source-manifest.tsv").read_text()), delimiter="\t"))
    names = set()
    for relative, sha, size in entries:
        need(re.fullmatch(r"[A-Za-z0-9_./-]+", relative) is not None and
             not relative.startswith("/") and ".." not in Path(relative).parts,
             "unsafe manifest path")
        need(relative not in names, "duplicate source member")
        names.add(relative)
        path = snapshot / relative
        need(path.is_file() and not path.is_symlink() and path.stat().st_size == int(size)
             and digest(path) == sha, f"source manifest mismatch: {relative}")
    actual = {p.relative_to(snapshot).as_posix() for p in snapshot.rglob("*") if p.is_file()}
    need(actual == names | {"source-manifest.tsv"}, "unlisted source file")
    need(digest(snapshot / "parent-source-manifest.tsv") == PARENT, "parent identity mismatch")
    parent = {p: h for p, h, _ in csv.reader(io.StringIO(
        (snapshot / "parent-source-manifest.tsv").read_text()), delimiter="\t")}
    plan = load(snapshot / "plan.json")
    need(plan["schema"] == "path2-subtree-replay-v1" and plan["parentSnapshot"] == PARENT
         and plan["parentBaseReadySha256"] == BASE_READY and plan["proofEvidence"] is False
         and plan["target"] == "879/2000" and plan["maximumWorkers"] == 32,
         "source contract mismatch")
    replacement = plan["replacedIndices"]
    need(len(set(replacement)) == len(replacement) and all(type(i) is int and 0 <= i < 10 for i in replacement),
         "invalid finite replacement indices")
    expected_ns = sorted(n for i in replacement
        for n in range(1 if i == 0 else 10*i+1, min(99,10*(i+1))+1))
    need(sorted(plan["ns"]) == expected_ns and len(set(plan["ns"])) == len(expected_ns), "missing n range")
    expected_reuse = [dict(index=i, module=m, theorem=t)
                      for i,(m,t) in enumerate(EXPECTED_TASK_PAIRS[:17]) if i not in replacement]
    need(plan["reusedRoots"] == expected_reuse, "wrong reused-root inventory")
    need(plan["topology"] == dict(index=17, module=EXPECTED_TASK_PAIRS[17][0], theorem=EXPECTED_TASK_PAIRS[17][1]),
         "wrong topology witness")
    need(plan["finalRoots"] == list(FINAL_ROOTS), "public final roots changed")
    sources = snapshot / "sources"
    imports = {}
    hashes = {}
    native = {}
    for path in sorted(sources.glob("*.lean")):
        module = path.stem
        text = path.read_text(encoding="utf-8")
        code = strip_lean_comments_and_strings(text, module)
        sites = list(re.finditer(r"\bnative_decide\b", code))
        need(len(sites) <= 1, "more than one native site per module")
        scan_source(path, module, native=bool(sites))
        if sites:
            declarations = re.findall(r"\btheorem\s+([A-Za-z0-9_]+)\s*:", code[:sites[0].start()])
            need(bool(declarations), "native site has no theorem owner")
            native[module] = declarations[-1]
        imports[module] = [m for row in re.findall(r"^\s*import\s+([^\n]+)$", code, flags=re.M) for m in row.split()]
        hashes[module] = digest(path)
    need(native == plan["nativeTheorems"], "native-site inventory differs from source")
    visited, active, order = set(), set(), []
    def visit(module: str) -> None:
        need(module not in active, "import cycle")
        if module in visited:
            return
        need(module in imports, "missing module")
        active.add(module)
        for dependency in imports[module]:
            if dependency.startswith("Path2"):
                visit(dependency)
        active.remove(module)
        visited.add(module)
        order.append(module)
    for module in FINAL_ROOTS:
        visit(module)
    need(set(order) == set(hashes) and order == plan["moduleOrder"] and imports == plan["imports"],
         "closure/import inventory mismatch")
    swapped = {EXPECTED_TASK_PAIRS[i][0] for i in replacement}
    parent_paths = list((snapshot / "parent-sources").glob("*.lean"))
    need(len(parent_paths) == 79, "parent source closure is not 79 modules")
    for path in parent_paths:
        module = path.stem
        need(digest(path) == parent[PREFIX+path.name], "parent source copy mismatch")
        if module not in swapped:
            need(hashes[module] == digest(path), f"unapproved parent modification: {module}")
        else:
            # The entire exported theorem type (all binders and quantifiers)
            # must be unchanged. Only the proof and imports can differ.
            pattern = r"theorem\s+\w+\s*:(.*?)\s*:=\s*by"
            old = re.findall(pattern, strip_lean_comments_and_strings(path.read_text(), module), re.S)
            new = re.findall(pattern, strip_lean_comments_and_strings((sources/path.name).read_text(), module), re.S)
            normal = lambda rows: [re.sub(r"\s+", " ", x).strip() for x in rows]
            need(len(old) == len(new) == 1 and normal(old) == normal(new), "batch theorem type changed")
    for module, sha in SUPPORT.items():
        need(hashes[module] == sha, "unreviewed optimized support source")
    numerical = plan["numericalTasks"]
    need(len({e["module"] for e in numerical}) == len(numerical) and
         [e["index"] for e in numerical] == list(range(len(numerical))), "duplicate/missing task index")
    need(sorted(e["n"] for e in plan["assemblies"]) == expected_ns, "per-n assembly missing")
    for n in expected_ns:
        rows = [e for e in numerical if e["n"] == n]
        cursor = 0
        for row in rows:
            need(row["firstLeaf"] == cursor and row["pastLeaf"] == cursor + row["leaves"]
                 and 1 <= row["leaves"] <= 128 and row["fuel"] == (6 if n < 11 else 5)
                 and row["sourceSha256"] == hashes[row["module"]]
                 and native[row["module"]] == row["theorem"], "bad finite partition identity")
            cursor = row["pastLeaf"]
        assembly = next(e for e in plan["assemblies"] if e["n"] == n)
        need(cursor == assembly["leaves"] and len(rows) == assembly["shards"] and
             imports[assembly["module"]] == [e["module"] for e in rows] and
             native[assembly["module"]] == assembly["parsedTheorem"], "per-n coverage inventory mismatch")
    need(set(native) == {e["module"] for e in numerical + plan["assemblies"] + expected_reuse + [plan["topology"]]},
         "unaccounted native theorem")
    plan = dict(plan, snapshotId=sid)
    return plan, hashes


def verify_evidence(snapshot: Path, build: Path, *, final: bool = False) -> dict:
    plan, hashes = preflight(snapshot)
    base = load(build / "BASE_READY.json")
    need(base["snapshotId"] == plan["snapshotId"] and base["parentSnapshot"] == PARENT and
         base["parentBaseReadySha256"] == BASE_READY and "4.29.1" in base["leanVersion"], "base identity mismatch")
    external = load(build/"EXTERNAL_READY.json")
    need(digest(build/"EXTERNAL_READY.json") == base["externalReadySha256"] and
         external["snapshotId"] == plan["snapshotId"] and external["parentSnapshot"] == PARENT
         and external["proofEvidence"] is False, "external dependency receipt mismatch")
    parent = {p:h for p,h,_ in csv.reader(io.StringIO((snapshot/"parent-source-manifest.tsv").read_text()), delimiter="\t")}
    reachable = set()
    def visit_external(module):
        if not module.startswith("BerryEsseen.") or module in reachable:
            return
        reachable.add(module)
        record = external["modules"][module]
        relative = Path(*module.split("."))
        source = (build/"external"/relative).with_suffix(".lean")
        need(digest(source) == record["sourceSha256"] == parent["projects/berry-esseen/lean/"+relative.as_posix()+".lean"]
             and digest(source.with_suffix(".olean")) == record["oleanSha256"], "external source/olean identity mismatch")
        code = strip_lean_comments_and_strings(source.read_text(encoding="utf-8"), module)
        imports = [m for row in re.findall(r"^\s*import\s+([^\n]+)$",code,re.M) for m in row.split()]
        need(imports == record["imports"] and record["proofEvidence"] is False, "external import identity mismatch")
        if record["role"] == "new-parent-dependency":
            need(record["exitCode"] == 0, "external compilation failed")
            for kind in ["log","time"]:
                need(digest(build/record[kind+"Path"]) == record[kind+"Sha256"], "external build artifact mismatch")
            need("sorryAx" not in (build/record["logPath"]).read_text(), "external sorry")
        else:
            need(record["role"] == "reused-parent-dependency", "unknown external role")
        for dependency in imports:
            visit_external(dependency)
    for module in plan["externalImports"]:
        visit_external(module)
    need(reachable == set(external["modules"]), "external closure mismatch")
    records = {}
    for path in sorted((build / "records").glob("*.json")):
        value = load(path)
        module = path.stem
        need(module in hashes and value["module"] == module and
             value["snapshotId"] == plan["snapshotId"] and value["sourceSha256"] == hashes[module]
             and value["exitCode"] == 0 and value["proofEvidence"] is False,
             "checkpoint identity mismatch")
        need(digest(build / "Path2" / f"{module}.olean") == value["oleanSha256"], "checkpoint olean mismatch")
        need(digest(build / "Path2" / f"{module}.lean") == hashes[module], "build source changed")
        if value["role"] == "reused-parent-native":
            legacy = load(build / "reused" / module / "result.json")
            need(digest(build / "reused" / module / "result.json") == value["parentResultSha256"] and
                 legacy["snapshotId"] == PARENT and legacy["sourceSha256"].lower() == hashes[module] and
                 legacy["oleanSha256"].lower() == value["oleanSha256"] and
                 legacy["baseReadySha256"].lower() == BASE_READY and legacy["exitCode"] == 0 and
                 value["parentEffectiveJobId"] == f'{legacy["slurmArrayJobId"]}_{legacy["taskIndex"]}' and
                 str(legacy["slurmArrayTaskId"]) == str(legacy["taskIndex"]) and
                 value["parentSlurmState"] == "COMPLETED|0:0", "reused proof mismatch")
            for kind in ["log", "time"]:
                need(digest(build/"reused"/module/(kind+".txt")) == legacy[kind+"Sha256"].lower(), "legacy log mismatch")
        elif value["role"] == "reused-parent-analytic":
            need(value["parentSnapshot"] == PARENT, "analytic parent mismatch")
        else:
            need(value["dependencyLeanPath"] == base["dependencyLeanPath"], "dependency search path changed")
            audit_runtime_record(build, build/"Path2", value)
        records[module] = value
    for module, sha in base["recordHashes"].items():
        need(digest(build/"records"/(module+".json")) == sha, "prepared dependency record changed")
    for module, record in records.items():
        if "imports" in record:
            need(record["imports"] == {m: records[m]["oleanSha256"]
                 for m in plan["imports"][module] if m in hashes}, "compiled dependency identity mismatch")
    result = dict(schema="path2-subtree-evidence-v1", status="PASS", proofEvidence=False,
        snapshotId=plan["snapshotId"], moduleCount=len(hashes), checkedModules=len(records),
        nativeAxiomCount=len(plan["nativeTheorems"]), completeLeanReplay=final,
        target="879/2000", recordHashes={m: digest(build/"records"/(m+".json")) for m in records})
    if final:
        need(set(records) == set(hashes), "final module missing")
        result["literalInputHashes"] = audit_literal_inputs(snapshot, build)
        execution_repair_paths(build)
        result["executionRepairSha256"] = digest(build / "EXECUTION_REPAIR.json")
        fresh = build / "fresh"
        fresh_records = {}
        for module in plan["moduleOrder"]:
            path = fresh/"records"/(module+".json")
            record = load(path)
            need(record["sourceSha256"] == hashes[module] and record["snapshotId"] == plan["snapshotId"]
                 and record["module"] == module and record["proofEvidence"] is False
                 and digest(fresh/"Path2"/(module+".lean")) == hashes[module]
                 and record["exitCode"] == 0 and digest(fresh/"Path2"/(module+".olean")) == record["oleanSha256"],
                 "fresh final identity mismatch")
            if module in plan["nativeTheorems"]:
                need(digest(path) == result["recordHashes"][module], "fresh native witness changed")
            else:
                need(record["role"] == "fresh-final-analytic", "analytic module not freshly checked")
                need(record["dependencyLeanPath"] == base["dependencyLeanPath"], "fresh dependency search path changed")
                audit_runtime_record(build, fresh/"Path2", record)
            fresh_records[module] = record
        for module, record in fresh_records.items():
            if module not in plan["nativeTheorems"]:
                need(record["imports"] == {m:fresh_records[m]["oleanSha256"]
                     for m in plan["imports"][module] if m in hashes}, "fresh dependency identity mismatch")
        audit_module = "Path2Post044TargetAwareConcreteFinalAxiomAudit"
        text = (build/fresh_records[audit_module]["logPath"]).read_text()
        lists = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text, re.S)
        need(len(lists) == 1, "final axiom log missing/ambiguous")
        axioms = [x.strip().strip("'").removeprefix("BerryEsseen.") for x in lists[0].split(",")]
        expected = STANDARDS | {t+"._native.native_decide.ax_1_1" for t in plan["nativeTheorems"].values()}
        need(len(axioms) == len(set(axioms)) and set(axioms) == expected, "final exact axiom set mismatch")
        result.update(finalTheorem="BerryEsseen.iidBerryEsseen879_2000_targetAware", finalAxioms=sorted(axioms),
            freshRecordHashes={m:digest(fresh/"records"/(m+".json")) for m in fresh_records})
    return result


def audit_runtime_record(build: Path, sources: Path, value: dict) -> None:
    for kind in ["log", "time"]:
        relative = value[kind+"Path"]
        path = build / relative
        need(not Path(relative).is_absolute() and ".." not in Path(relative).parts and
             path.is_file() and digest(path) == value[kind+"Sha256"], "runtime artifact mismatch")
    log = build/value["logPath"]
    need("sorryAx" not in log.read_text() and value["elapsedSeconds"] >= 0, "invalid Lean log/timing")
    module = value["module"]
    remote = "/work/stat-grad/xhn/berry_esseen_path2/builds/"+value["snapshotId"]
    source_relative = sources.relative_to(build).as_posix()
    remote_sources = remote+"/"+source_relative
    parent_sources = "/work/stat-grad/xhn/berry_esseen_path2/builds/"+PARENT+"/workspace/projects/berry-esseen/lean/Path2"
    prefix = remote_sources+":"+(remote+"/Path2:" if source_relative.startswith("fresh/") else "")
    lean_path = prefix+remote+"/external:"+parent_sources+":"+value["dependencyLeanPath"]
    attempt = Path(value["logPath"]).parent.as_posix()
    expected = ["/usr/bin/time", "-v", "-o", remote+"/"+value["timePath"], "lake", "env", "env",
                "LEAN_PATH="+lean_path, "lean", "-j1", "--tstack=32768", "-R", remote_sources,
                "-o", remote+"/"+attempt+"/"+module+".olean", remote_sources+"/"+module+".lean"]
    need(value["command"] == expected, "unexpected Lean invocation")


def artifact_paths(snapshot: Path, build: Path) -> list[Path]:
    """Exact portable evidence set; mutable queues and failed attempts are excluded."""
    paths = {p for p in snapshot.rglob("*") if p.is_file()}
    paths.update(build / "fresh" / relative for relative in literal_inputs(snapshot))
    paths.update(execution_repair_paths(build))
    paths.update(build/name for name in ["BASE_READY.json", "PILOT_READY.json", "EXTERNAL_READY.json",
                 "CUTOVER_INTENT.json", "CUTOVER_READY.json"])
    paths.update(p for p in (build/"external").rglob("*") if p.is_file())
    for record in load(build/"EXTERNAL_READY.json")["modules"].values():
        if "logPath" in record:
            paths.update(build/record[k+"Path"] for k in ["log", "time"])
    plan = load(snapshot/"plan.json")
    for prefix in [build, build/"fresh"]:
        for module in plan["moduleOrder"]:
            record_path = prefix/"records"/(module+".json")
            record = load(record_path)
            paths.add(record_path)
            paths.update(prefix/"Path2"/(module+ext) for ext in [".lean", ".olean"])
            if "logPath" in record:
                paths.update(build/record[k+"Path"] for k in ["log", "time"])
            if record["role"] == "reused-parent-native":
                paths.update(build/"reused"/module/name for name in ["result.json", "log.txt", "time.txt"])
    return sorted(paths)


def extract_bundle(archive: Path, sha256: str, destination: Path, sid: str) -> dict:
    need(re.fullmatch(r"[0-9a-f]{64}", sid) is not None, "invalid snapshot ID")
    need(digest(archive) == sha256, "evidence archive hash mismatch")
    need(not destination.exists(), "refusing existing extraction directory")
    destination.mkdir(parents=True)
    with tarfile.open(archive, "r:gz") as handle:
        members = handle.getmembers()
        names = [m.name for m in members]
        need(len(names) == len(set(names)) and len(names) < 50000 and
             sum(m.size for m in members) < 20_000_000_000, "invalid evidence archive size/inventory")
        for member in members:
            need(member.isfile() and re.fullmatch(r"[A-Za-z0-9_./-]+", member.name) is not None
                 and ".." not in Path(member.name).parts
                 and member.name.startswith((f"snapshots/{sid}/", f"builds/{sid}/")),
                 "unsafe evidence member")
        for member in members:
            path = destination/member.name
            path.parent.mkdir(parents=True, exist_ok=True)
            with handle.extractfile(member) as source, path.open("xb") as target:
                shutil.copyfileobj(source, target)
    snapshot, build = destination/"snapshots"/sid, destination/"builds"/sid
    manifest = build/"evidence-manifest.tsv"
    entries = list(csv.reader(io.StringIO(manifest.read_text()), delimiter="\t"))
    inventory = {relative for relative, _, _ in entries}
    need(len(inventory) == len(entries), "duplicate evidence manifest entry")
    need(set(names) == inventory | {f"builds/{sid}/evidence-manifest.tsv", f"builds/{sid}/FINAL_READY.json"},
         "evidence archive inventory mismatch")
    for relative, sha, size in entries:
        need(relative in names and (destination/relative).stat().st_size == int(size)
             and digest(destination/relative) == sha, "evidence manifest mismatch")
    need({p.relative_to(destination).as_posix() for p in artifact_paths(snapshot,build)} == inventory,
         "evidence inventory does not match accepted records")
    receipt = verify_evidence(snapshot, build, final=True)
    saved = load(build/"FINAL_READY.json")
    need(saved == dict(receipt, evidenceManifestSha256=digest(manifest), artifactCount=len(entries)),
         "saved final receipt differs from independent verification")
    return receipt


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path, nargs="?")
    parser.add_argument("--build", type=Path)
    parser.add_argument("--final", action="store_true")
    parser.add_argument("--extract", type=Path)
    parser.add_argument("--sha256")
    parser.add_argument("--destination", type=Path)
    parser.add_argument("--snapshot-id")
    args = parser.parse_args()
    if args.extract:
        result = extract_bundle(args.extract, args.sha256, args.destination, args.snapshot_id)
    elif args.build:
        result = verify_evidence(args.snapshot, args.build, final=args.final)
    else:
        plan, hashes = preflight(args.snapshot)
        result = dict(status="PASS", snapshotId=plan["snapshotId"], modules=len(hashes),
                      nativeAxioms=len(plan["nativeTheorems"]), proofEvidence=False)
    print(json.dumps(result, sort_keys=True, indent=2))
