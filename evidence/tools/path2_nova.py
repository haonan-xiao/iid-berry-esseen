#!/usr/bin/env python3
"""Prepare a source-bound build and run exact certificates or diagnostics."""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import socket
import stat
import subprocess
import sys
import tarfile
import tempfile
import time


IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*$")
INCLUDE_RE = re.compile(r'include_str\s+"([^"]+)"')
AXIOM_PRINT_RE = re.compile(r"^\s*#print\s+axioms\s+(\S+)\s*$")
FORBIDDEN_SOURCE_TOKENS = ("axiom", "opaque", "unsafe", "sorry", "admit")
SOURCE_TOKEN_BOUNDARY = r"[A-Za-z0-9_']"
RESEARCH_PATH2_SOURCE_ROOT = ".runtime/berry-esseen-path2"
FINAL_PATH2_SOURCE_ROOT = "projects/berry-esseen/lean/Path2"
FINAL_ROOTS = [
    "Path2Post044TargetAwareConcreteCertificateAxiomAudit",
    "Path2Post044TargetAwareConcreteFinalAxiomAudit",
    "Path2Post044TargetAwareAxiomAudit",
    "Path2Post044InterfaceDominanceAudit",
    "Path2Post044FiniteTargetAwareFuelMonotonicityAxiomAudit",
    "Path2Post044FiniteTargetAwareDiagnosticCorrectnessAxiomAudit",
]
FINAL_PROOF_CONTRACT = {
    "ready": True,
    "sourceRoot": FINAL_PATH2_SOURCE_ROOT,
    "finiteFirstBatchFuel": 6,
    "finiteLaterBatchFuel": 5,
    "middleFuel": 5,
    "upperFuel": 8,
    "nativeCertificateCount": 18,
    "proofRootCount": 6,
}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def strip_lean_comments_and_strings(source: str, module: str) -> str:
    """Mask nested comments, strings, and character literals fail-closed."""
    output: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False

    def char_literal_end(start: int) -> int | None:
        cursor = start + 1
        if cursor >= len(source):
            return None
        if source[cursor] == "\\":
            cursor += 1
            if cursor >= len(source):
                return None
            if source[cursor:cursor + 2] == "u{":
                closing_brace = source.find("}", cursor + 2)
                if closing_brace < 0:
                    return None
                cursor = closing_brace + 1
            else:
                cursor += 1
        else:
            cursor += 1
        if cursor < len(source) and source[cursor] == "'":
            return cursor + 1
        return None

    while index < len(source):
        char = source[index]
        pair = source[index:index + 2]
        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                output.append("\n")
            else:
                output.append(" ")
            index += 1
            continue
        if block_depth:
            if pair == "/-":
                output.extend((" ", " "))
                block_depth += 1
                index += 2
            elif pair == "-/":
                output.extend((" ", " "))
                block_depth -= 1
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "--":
            output.extend((" ", " "))
            in_line_comment = True
            index += 2
        elif pair == "/-":
            output.extend((" ", " "))
            block_depth = 1
            index += 2
        elif char == "'" and (char_end := char_literal_end(index)) is not None:
            output.extend(
                "\n" if value == "\n" else " "
                for value in source[index:char_end])
            index = char_end
        elif char == '"':
            output.append(" ")
            in_string = True
            index += 1
        else:
            output.append(char)
            index += 1
    if block_depth != 0:
        raise RuntimeError(f"unterminated Lean block comment in {module}")
    if in_string:
        raise RuntimeError(f"unterminated Lean string in {module}")
    return "".join(output)


def source_token_matches(source: str, token: str) -> list[re.Match[str]]:
    return list(re.finditer(
        rf"(?<!{SOURCE_TOKEN_BOUNDARY}){re.escape(token)}"
        rf"(?!{SOURCE_TOKEN_BOUNDARY})", source))


def source_line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def scan_final_source(source: str, module: str, *, native: bool) -> None:
    code = strip_lean_comments_and_strings(source, module)
    for token in FORBIDDEN_SOURCE_TOKENS:
        matches = source_token_matches(code, token)
        if matches:
            raise RuntimeError(
                f"forbidden source token {token!r} in {module} at line "
                f"{source_line_number(code, matches[0].start())}")
    native_count = len(source_token_matches(code, "native_decide"))
    expected = 1 if native else 0
    if native_count != expected:
        raise RuntimeError(
            f"{module}: expected {expected} native_decide tokens, "
            f"found {native_count}")


def atomic_write_bytes(path: Path, content: bytes) -> None:
    """Publish one immutable evidence file without exposing partial bytes."""
    if path.exists():
        raise RuntimeError(f"refusing to overwrite evidence file: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary_name, path)
    except Exception:
        try:
            os.close(descriptor)
        except OSError:
            pass
        Path(temporary_name).unlink(missing_ok=True)
        raise


def publish_final_evidence_bundle(
        nova_root: Path, run_root: Path, artifact_paths: list[Path],
        final_ready: dict) -> tuple[dict, dict]:
    """Publish a source-bound inventory, FINAL_READY, and portable archive.

    The manifest lists the pre-existing proof artifacts but not itself or
    FINAL_READY.  FINAL_READY records the manifest hash and exact entry count;
    the archive then carries all three layers under paths relative to the Nova
    project root.  The independent workstation verifier rejects an incomplete
    extraction even if the transfer archive itself is not retained.
    """
    nova_root = nova_root.resolve()
    run_root = run_root.resolve()
    try:
        run_root.relative_to(nova_root)
    except ValueError as error:
        raise RuntimeError("final run root escapes the Nova project root") from error

    records: dict[str, tuple[Path, str, int]] = {}
    for raw_path in artifact_paths:
        path = raw_path.resolve()
        if not path.is_file():
            raise RuntimeError(f"final evidence artifact is missing: {path}")
        try:
            relative = path.relative_to(nova_root).as_posix()
        except ValueError as error:
            raise RuntimeError(
                f"final evidence artifact escapes the Nova root: {path}") from error
        records[relative] = (path, sha256_file(path).upper(), path.stat().st_size)
    if len(records) != 256:
        raise RuntimeError(
            f"expected 256 distinct final evidence artifacts, got {len(records)}")

    manifest_text = "".join(
        f"{relative}\t{digest}\t{byte_count}\n"
        for relative, (_, digest, byte_count) in sorted(records.items()))
    manifest_bytes = manifest_text.encode("utf-8")
    manifest_hash = hashlib.sha256(manifest_bytes).hexdigest().upper()
    manifest_path = run_root / "FINAL_EVIDENCE_MANIFEST.tsv"

    enriched_ready = dict(final_ready)
    enriched_ready.update({
        "evidenceManifestPath": str(manifest_path),
        "evidenceManifestSha256": manifest_hash,
        "evidenceArtifactCount": len(records),
    })
    ready_bytes = (
        json.dumps(enriched_ready, indent=2, sort_keys=True) + "\n").encode(
            "utf-8")
    ready_hash = hashlib.sha256(ready_bytes).hexdigest().upper()
    ready_path = run_root / "FINAL_READY.json"
    archive_path = run_root / "FINAL_EVIDENCE.tar.gz"
    archive_hash_path = run_root / "FINAL_EVIDENCE.tar.gz.sha256"
    publication_paths = [
        manifest_path, ready_path, archive_path, archive_hash_path]
    collisions = [path for path in publication_paths if path.exists()]
    if collisions:
        raise RuntimeError(
            f"refusing to overwrite final evidence output: {collisions[0]}")

    descriptor, temporary_name = tempfile.mkstemp(
        prefix=".FINAL_EVIDENCE.", suffix=".tar.gz.tmp", dir=run_root)
    os.close(descriptor)
    temporary_path = Path(temporary_name)
    published: list[Path] = []
    try:
        # Level 1 keeps the one-time transfer bundle cheap relative to the
        # proof computation while still avoiding hundreds of browser files.
        with tarfile.open(temporary_path, mode="w:gz", compresslevel=1) as archive:
            for path, content in (
                    (manifest_path, manifest_bytes),
                    (ready_path, ready_bytes)):
                info = tarfile.TarInfo(
                    name=path.relative_to(nova_root).as_posix())
                info.size = len(content)
                info.mtime = int(final_ready["finishedAtUnix"])
                info.mode = 0o444
                archive.addfile(info, io.BytesIO(content))
            for relative, (path, _, _) in sorted(records.items()):
                archive.add(path, arcname=relative, recursive=False)
        with temporary_path.open("rb+") as handle:
            os.fsync(handle.fileno())
        archive_hash = sha256_file(temporary_path).upper()
        archive_hash_bytes = (
            f"{archive_hash}  {archive_path.name}\n").encode("ascii")
        os.replace(temporary_path, archive_path)
        published.append(archive_path)
        atomic_write_bytes(archive_hash_path, archive_hash_bytes)
        published.append(archive_hash_path)
        atomic_write_bytes(manifest_path, manifest_bytes)
        published.append(manifest_path)
        # FINAL_READY is the commit point.  No fallible filesystem operation
        # follows its atomic publication.
        atomic_write_bytes(ready_path, ready_bytes)
        published.append(ready_path)
    except Exception:
        temporary_path.unlink(missing_ok=True)
        if ready_path not in published:
            for path in reversed(published):
                path.unlink(missing_ok=True)
        raise
    return enriched_ready, {
        "finalReadyPath": str(ready_path),
        "finalReadySha256": ready_hash,
        "evidenceManifestPath": str(manifest_path),
        "evidenceManifestSha256": manifest_hash,
        "evidenceArtifactCount": len(records),
        "evidenceArchivePath": str(archive_path),
        "evidenceArchiveSha256": archive_hash,
        "evidenceArchiveSha256Path": str(archive_hash_path),
    }


def run(command: list[str], *, cwd: Path, env: dict[str, str] | None = None,
        stdout=None, stderr=None) -> None:
    print("+", " ".join(command), flush=True)
    subprocess.run(command, cwd=cwd, env=env, check=True,
                   stdout=stdout, stderr=stderr)


def validate_snapshot_metadata(metadata: object, snapshot_id: str) -> dict:
    if not isinstance(metadata, dict):
        raise RuntimeError("snapshot metadata must be a JSON object")
    if (type(metadata.get("schemaVersion")) is not int or
            metadata.get("schemaVersion") != 2):
        raise RuntimeError("snapshot metadata schemaVersion must be 2")
    if metadata.get("snapshotId") != snapshot_id:
        raise RuntimeError("snapshot metadata ID does not match the job")

    kind = metadata.get("snapshotKind")
    source_root = metadata.get("path2SourceRoot")
    if kind == "research":
        if source_root != RESEARCH_PATH2_SOURCE_ROOT:
            raise RuntimeError("research snapshot has the wrong Path 2 source root")
        if "finalProofSnapshot" in metadata:
            raise RuntimeError("research snapshot claims final-proof readiness")
    elif kind == "final-proof":
        if source_root != FINAL_PATH2_SOURCE_ROOT:
            raise RuntimeError("final snapshot has the wrong Path 2 source root")
        if metadata.get("roots") != FINAL_ROOTS:
            raise RuntimeError("final snapshot roots do not match the six proof roots")
        if (type(metadata.get("path2ModuleCount")) is not int or
                metadata.get("path2ModuleCount") != 79):
            raise RuntimeError("final snapshot does not have the 79-module proof closure")
        contract = metadata.get("finalProofSnapshot")
        if not isinstance(contract, dict):
            raise RuntimeError("final snapshot lacks finalProofSnapshot metadata")
        for key, expected in FINAL_PROOF_CONTRACT.items():
            actual = contract.get(key)
            if type(actual) is not type(expected) or actual != expected:
                raise RuntimeError(
                    f"finalProofSnapshot.{key} must equal {expected!r}")
    else:
        raise RuntimeError(f"unsupported snapshot kind: {kind!r}")
    return metadata


def load_snapshot_metadata(snapshot_root: Path, snapshot_id: str) -> dict:
    path = snapshot_root / "snapshot.json"
    if not path.is_file():
        raise RuntimeError(f"snapshot metadata is missing: {path}")
    try:
        metadata = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise RuntimeError(f"cannot read snapshot metadata: {path}") from error
    return validate_snapshot_metadata(metadata, snapshot_id)


def path2_source_dir(workspace: Path, metadata: dict, *,
                     require_final: bool = False) -> Path:
    if require_final and metadata["snapshotKind"] != "final-proof":
        raise RuntimeError("final proof operation requires a final-proof snapshot")
    relative = metadata["path2SourceRoot"]
    source = workspace / Path(relative)
    if not source.is_dir():
        raise RuntimeError(f"Path 2 source root is missing: {source}")
    return source


def verify_base_ready_identity(ready_data: object, snapshot_id: str,
                               metadata: dict, context: str) -> None:
    if not isinstance(ready_data, dict):
        raise RuntimeError(f"BASE_READY is not an object during {context}")
    if ready_data.get("snapshotId") != snapshot_id:
        raise RuntimeError(f"BASE_READY snapshot ID does not match {context}")
    if ready_data.get("snapshotKind") != metadata["snapshotKind"]:
        raise RuntimeError(f"BASE_READY snapshot kind does not match {context}")
    if ready_data.get("path2SourceRoot") != metadata["path2SourceRoot"]:
        raise RuntimeError(f"BASE_READY Path 2 source root does not match {context}")


def verify_snapshot(snapshot_root: Path, snapshot_id: str) -> dict:
    metadata = load_snapshot_metadata(snapshot_root, snapshot_id)
    manifest = snapshot_root / "source-manifest.tsv"
    if sha256_file(manifest) != snapshot_id:
        raise RuntimeError("source manifest hash does not equal snapshot ID")
    workspace = snapshot_root / "workspace"
    with manifest.open("r", encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if len(row) != 3:
                raise RuntimeError(f"malformed manifest row: {row!r}")
            relative, expected_hash, expected_size = row
            path = workspace / Path(relative)
            if not path.is_file():
                raise RuntimeError(f"snapshot file is missing: {relative}")
            if path.stat().st_size != int(expected_size):
                raise RuntimeError(f"snapshot size mismatch: {relative}")
            if sha256_file(path) != expected_hash:
                raise RuntimeError(f"snapshot hash mismatch: {relative}")
    return metadata


def verify_build_sources(snapshot_root: Path, build_workspace: Path) -> None:
    """Check every source-bound input copied into the mutable build tree."""
    manifest = snapshot_root / "source-manifest.tsv"
    with manifest.open("r", encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if len(row) != 3:
                raise RuntimeError(f"malformed manifest row: {row!r}")
            relative, expected_hash, expected_size = row
            path = build_workspace / Path(relative)
            if not path.is_file():
                raise RuntimeError(f"build input is missing: {relative}")
            if path.stat().st_size != int(expected_size):
                raise RuntimeError(f"build input size mismatch: {relative}")
            if sha256_file(path) != expected_hash:
                raise RuntimeError(f"build input hash mismatch: {relative}")


def parse_imports(path: Path) -> list[str]:
    imports: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            imports.extend(match.group(1).split())
    return imports


def path2_closure(runtime: Path, roots: list[str]) -> tuple[list[str], list[str]]:
    visited: set[str] = set()
    visiting: set[str] = set()
    order: list[str] = []
    external: set[str] = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        if module in visiting:
            raise RuntimeError(f"Path 2 import cycle at {module}")
        visiting.add(module)
        source = runtime / f"{module}.lean"
        if not source.is_file():
            raise RuntimeError(f"missing Path 2 source: {source}")
        for imported in parse_imports(source):
            if imported.startswith("Path2"):
                visit(imported)
            else:
                external.add(imported)
        visiting.remove(module)
        visited.add(module)
        order.append(module)

    for root in roots:
        visit(root)
    return order, sorted(external)


def make_writable(path: Path) -> None:
    for item in [path, *path.rglob("*")]:
        mode = item.stat().st_mode
        item.chmod(mode | stat.S_IWUSR)


def lean_command(lean_project: Path, runtime: Path, module: str,
                 output: Path) -> list[str]:
    return [
        "lake", "env", "lean", "--tstack=32768", "-R", str(runtime),
        "-o", str(output), str(runtime / f"{module}.lean"),
    ]


def prepare(args: argparse.Namespace) -> None:
    snapshot_id = os.environ["BERRY_SNAPSHOT_ID"]
    snapshot_root = Path(os.environ["BERRY_SNAPSHOT_ROOT"])
    build_root = Path(os.environ["BERRY_BUILD_ROOT"])
    metadata = verify_snapshot(snapshot_root, snapshot_id)

    source_workspace = snapshot_root / "workspace"
    build_workspace = build_root / "workspace"
    if not build_workspace.exists():
        build_root.mkdir(parents=True, exist_ok=True)
        shutil.copytree(source_workspace, build_workspace)
        make_writable(build_workspace)

        seed_id = os.environ.get("BERRY_SEED_BUILD_ID", "")
        if seed_id:
            if not re.fullmatch(r"[0-9a-f]{64}", seed_id):
                raise RuntimeError(f"invalid BERRY_SEED_BUILD_ID: {seed_id}")
            nova_root = Path(os.environ["BERRY_NOVA_ROOT"])
            seed_lean = (nova_root / "builds" / seed_id / "workspace" /
                         "projects/berry-esseen/lean")
            target_lean = build_workspace / "projects/berry-esseen/lean"
            seed_manifest = seed_lean / "lake-manifest.json"
            target_manifest = target_lean / "lake-manifest.json"
            seed_packages = seed_lean / ".lake/packages"
            target_packages = target_lean / ".lake/packages"
            if not seed_manifest.is_file() or not seed_packages.is_dir():
                raise RuntimeError(f"seed build is incomplete: {seed_lean}")
            if sha256_file(seed_manifest) != sha256_file(target_manifest):
                raise RuntimeError("seed and target Lake manifests differ")
            target_packages.parent.mkdir(parents=True, exist_ok=True)
            shutil.copytree(seed_packages, target_packages, symlinks=True)
            print(f"seeded Lake dependency tree from {seed_id}", flush=True)

    # A retry may encounter a partially prepared mutable build.  Reject any
    # missing or changed manifest-bound source before spending CPU on Lake or
    # Lean; generated package/build artifacts are intentionally outside this
    # source-identity check.
    verify_build_sources(snapshot_root, build_workspace)
    lean_project = build_workspace / "projects/berry-esseen/lean"
    runtime = path2_source_dir(build_workspace, metadata)
    order, external = path2_closure(runtime, args.root)
    berry_targets = [module for module in external
                     if module.startswith("BerryEsseen.")]
    roots = set(args.root)
    if metadata["snapshotKind"] == "final-proof":
        for module in order:
            if module in roots:
                continue
            source = runtime / f"{module}.lean"
            scan_final_source(
                source.read_text(encoding="utf-8"), module, native=False)

    run(["lake", "exe", "cache", "get"], cwd=lean_project)
    if berry_targets:
        run(["lake", "build", *berry_targets], cwd=lean_project)

    environment = os.environ.copy()
    old_lean_path = environment.get("LEAN_PATH", "")
    environment["LEAN_PATH"] = str(runtime) + (
        os.pathsep + old_lean_path if old_lean_path else "")
    for module in order:
        if module in roots:
            continue
        source = runtime / f"{module}.lean"
        source_text = source.read_text(encoding="utf-8")
        if (metadata["snapshotKind"] != "final-proof" and
                source_token_matches(
                strip_lean_comments_and_strings(source_text, module),
                "native_decide")):
            raise RuntimeError(
                f"base closure unexpectedly contains native_decide: {module}")
        output = runtime / f"{module}.olean"
        run(lean_command(lean_project, runtime, module, output),
            cwd=lean_project, env=environment)

    versions = {
        "snapshotId": snapshot_id,
        "preparedAtUnix": time.time(),
        "hostname": socket.gethostname(),
        "roots": args.root,
        "snapshotKind": metadata["snapshotKind"],
        "path2SourceRoot": metadata["path2SourceRoot"],
        "seedBuildId": os.environ.get("BERRY_SEED_BUILD_ID") or None,
        "path2DependencyCount": len(order) - len(roots),
        "externalImports": external,
        "leanVersion": subprocess.check_output(
            ["lean", "--version"], cwd=lean_project, text=True).strip(),
        "lakeVersion": subprocess.check_output(
            ["lake", "--version"], cwd=lean_project, text=True).strip(),
    }
    ready = build_root / "BASE_READY.json"
    ready.write_text(json.dumps(versions, indent=2, sort_keys=True) + "\n",
                     encoding="utf-8")
    print(json.dumps(versions, indent=2, sort_keys=True))


def load_task(task_file: Path, index: int) -> dict[str, str]:
    with task_file.open("r", encoding="utf-8", newline="") as stream:
        tasks = list(csv.DictReader(stream, delimiter="\t"))
    if index < 0 or index >= len(tasks):
        raise RuntimeError(f"task index {index} is outside 0..{len(tasks) - 1}")
    return tasks[index]


def certificate(args: argparse.Namespace) -> None:
    snapshot_id = os.environ["BERRY_SNAPSHOT_ID"]
    snapshot_root = Path(os.environ["BERRY_SNAPSHOT_ROOT"])
    build_root = Path(os.environ["BERRY_BUILD_ROOT"])
    build_workspace = build_root / "workspace"
    lean_project = build_workspace / "projects/berry-esseen/lean"
    metadata = load_snapshot_metadata(snapshot_root, snapshot_id)
    runtime = path2_source_dir(build_workspace, metadata)
    ready = build_root / "BASE_READY.json"
    if not ready.is_file():
        raise RuntimeError(f"base build is not ready: {ready}")

    task_file = (snapshot_root / "workspace" /
                 "projects/berry-esseen/lean/scripts/nova/benchmark-tasks.tsv")
    task = load_task(task_file, args.index)
    module = task["module"]
    source = runtime / f"{module}.lean"
    actual_source_hash = sha256_file(source).upper()
    if actual_source_hash != task["sha256"].upper():
        raise RuntimeError(f"pinned source hash mismatch for {module}")

    run_id = os.environ.get(
        "BERRY_RUN_ID",
        f"benchmark-{os.environ.get('SLURM_ARRAY_JOB_ID', 'manual')}")
    run_root = Path(os.environ["BERRY_NOVA_ROOT"]) / "runs" / run_id
    run_root.mkdir(parents=True, exist_ok=True)
    stem = f"{args.index:02d}-{task['key']}"
    log_path = run_root / f"{stem}.log"
    time_path = run_root / f"{stem}.time.txt"
    result_path = run_root / f"{stem}.result.json"
    output = runtime / f"{module}.olean"

    environment = os.environ.copy()
    old_lean_path = environment.get("LEAN_PATH", "")
    environment["LEAN_PATH"] = str(runtime) + (
        os.pathsep + old_lean_path if old_lean_path else "")
    command = ["/usr/bin/time", "-v", "-o", str(time_path),
               *lean_command(lean_project, runtime, module, output)]
    started = time.time()
    return_code = 1
    with log_path.open("w", encoding="utf-8") as log:
        completed = subprocess.run(command, cwd=lean_project, env=environment,
                                   stdout=log, stderr=subprocess.STDOUT)
        return_code = completed.returncode
    finished = time.time()

    result = {
        "purpose": "known-pass infrastructure benchmark",
        "proofEvidence": False,
        "snapshotId": snapshot_id,
        "baseReadySha256": sha256_file(ready).upper(),
        "baseReadyPath": str(ready),
        "task": task,
        "taskIndex": args.index,
        "hostname": socket.gethostname(),
        "slurmJobId": os.environ.get("SLURM_JOB_ID"),
        "slurmArrayJobId": os.environ.get("SLURM_ARRAY_JOB_ID"),
        "slurmArrayTaskId": os.environ.get("SLURM_ARRAY_TASK_ID"),
        "startedAtUnix": started,
        "finishedAtUnix": finished,
        "elapsedSeconds": finished - started,
        "exitCode": return_code,
        "sourceSha256": actual_source_hash,
        "command": command,
        "oleanSha256": sha256_file(output).upper()
        if return_code == 0 and output.is_file() else None,
        "oleanPath": str(output),
        "logPath": str(log_path),
        "timePath": str(time_path),
        "resultPath": str(result_path),
    }
    result_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
    if return_code != 0 or not output.is_file():
        raise RuntimeError(f"exact certificate failed: {module}")


def final_certificate_tasks(snapshot_root: Path, metadata: dict) -> list[dict[str, str]]:
    """Derive the final task map from the source-bound axiom-audit module."""
    runtime = path2_source_dir(
        snapshot_root / "workspace", metadata, require_final=True)
    audit = (runtime /
             "Path2Post044TargetAwareConcreteCertificateAxiomAudit.lean")
    if not audit.is_file():
        raise RuntimeError(f"final certificate audit is missing: {audit}")

    modules = [module for module in parse_imports(audit)
               if module.startswith("Path2")]
    theorems: list[str] = []
    for line in audit.read_text(encoding="utf-8").splitlines():
        match = AXIOM_PRINT_RE.match(line)
        if match:
            theorems.append(match.group(1))
    if len(modules) != 18 or len(set(modules)) != 18:
        raise RuntimeError(
            f"expected 18 distinct final native-root imports, got {modules!r}")
    if len(theorems) != 18 or len(set(theorems)) != 18:
        raise RuntimeError(
            f"expected 18 distinct final axiom targets, got {theorems!r}")

    tasks: list[dict[str, str]] = []
    for index, (module, theorem) in enumerate(zip(modules, theorems)):
        source = runtime / f"{module}.lean"
        if not source.is_file():
            raise RuntimeError(f"final certificate source is missing: {source}")
        text = source.read_text(encoding="utf-8")
        scan_final_source(text, module, native=True)
        theorem_pattern = re.compile(
            rf"\btheorem\s+{re.escape(theorem)}\s*:")
        if not theorem_pattern.search(text):
            raise RuntimeError(
                f"axiom target {theorem} is not declared by {module}")
        tasks.append({
            "key": f"final-{index:02d}",
            "module": module,
            "theorem": theorem,
            "sha256": sha256_file(source).upper(),
        })
    return tasks


def verify_final_base_ready_contract(ready_data: dict, runtime: Path,
                                     tasks: list[dict[str, str]],
                                     context: str) -> None:
    """Bind BASE_READY to the exact eighteen native roots it prepared."""
    expected_roots = [task["module"] for task in tasks]
    if ready_data.get("roots") != expected_roots:
        raise RuntimeError(
            f"BASE_READY roots do not match the final witness set during {context}")
    order, _ = path2_closure(runtime, expected_roots)
    expected_dependencies = len(order) - len(expected_roots)
    actual_dependencies = ready_data.get("path2DependencyCount")
    if (type(actual_dependencies) is not int or
            actual_dependencies != expected_dependencies):
        raise RuntimeError(
            "BASE_READY dependency count does not match the final witness "
            f"closure during {context}")


def final_certificate(args: argparse.Namespace) -> None:
    snapshot_id = os.environ["BERRY_SNAPSHOT_ID"]
    snapshot_root = Path(os.environ["BERRY_SNAPSHOT_ROOT"])
    build_root = Path(os.environ["BERRY_BUILD_ROOT"])
    build_workspace = build_root / "workspace"
    lean_project = build_workspace / "projects/berry-esseen/lean"
    ready = build_root / "BASE_READY.json"

    # The final wave is proof evidence, not a benchmark.  Recheck the immutable
    # source snapshot and the prepared-build identity in every independent
    # shard before evaluating its native theorem.
    metadata = verify_snapshot(snapshot_root, snapshot_id)
    runtime = path2_source_dir(build_workspace, metadata, require_final=True)
    verify_build_sources(snapshot_root, build_workspace)
    if not ready.is_file():
        raise RuntimeError(f"base build is not ready: {ready}")
    ready_data = json.loads(ready.read_text(encoding="utf-8"))
    verify_base_ready_identity(
        ready_data, snapshot_id, metadata, "the final-certificate job")

    tasks = final_certificate_tasks(snapshot_root, metadata)
    verify_final_base_ready_contract(
        ready_data, runtime, tasks, "the final-certificate job")
    if args.index < 0 or args.index >= len(tasks):
        raise RuntimeError(
            f"final task index {args.index} is outside 0..{len(tasks) - 1}")
    task = tasks[args.index]
    module = task["module"]
    source = runtime / f"{module}.lean"
    actual_source_hash = sha256_file(source).upper()
    if actual_source_hash != task["sha256"]:
        raise RuntimeError(f"source-bound task mismatch for {module}")

    array_job_id = os.environ.get("SLURM_ARRAY_JOB_ID", "manual")
    if not re.fullmatch(r"(?:\d+|manual)", array_job_id):
        raise RuntimeError(f"invalid SLURM_ARRAY_JOB_ID: {array_job_id}")
    run_id = os.environ.get(
        "BERRY_RUN_ID", f"final-certificates-{array_job_id}")
    run_root = Path(os.environ["BERRY_NOVA_ROOT"]) / "runs" / run_id
    run_root.mkdir(parents=True, exist_ok=True)
    stem = f"{args.index:02d}-{module}"
    log_path = run_root / f"{stem}.log"
    time_path = run_root / f"{stem}.time.txt"
    result_path = run_root / f"{stem}.result.json"
    output = runtime / f"{module}.olean"
    output.unlink(missing_ok=True)

    environment = os.environ.copy()
    old_lean_path = environment.get("LEAN_PATH", "")
    environment["LEAN_PATH"] = str(runtime) + (
        os.pathsep + old_lean_path if old_lean_path else "")
    command = ["/usr/bin/time", "-v", "-o", str(time_path),
               *lean_command(lean_project, runtime, module, output)]
    started = time.time()
    with log_path.open("w", encoding="utf-8") as log:
        completed = subprocess.run(command, cwd=lean_project, env=environment,
                                   stdout=log, stderr=subprocess.STDOUT)
    finished = time.time()

    output_ok = completed.returncode == 0 and output.is_file()
    result = {
        "purpose": "final source-bound native proof root",
        "proofEvidence": output_ok,
        "evidenceScope": (
            "one native proof root; final concrete assembly and "
            "trust audit remain required"),
        "snapshotId": snapshot_id,
        "snapshotKind": metadata["snapshotKind"],
        "path2SourceRoot": metadata["path2SourceRoot"],
        "baseReadySha256": sha256_file(ready).upper(),
        "baseReadyPath": str(ready),
        "task": task,
        "taskIndex": args.index,
        "finalTaskCount": len(tasks),
        "hostname": socket.gethostname(),
        "slurmJobId": os.environ.get("SLURM_JOB_ID"),
        "slurmArrayJobId": os.environ.get("SLURM_ARRAY_JOB_ID"),
        "slurmArrayTaskId": os.environ.get("SLURM_ARRAY_TASK_ID"),
        "startedAtUnix": started,
        "finishedAtUnix": finished,
        "elapsedSeconds": finished - started,
        "exitCode": completed.returncode,
        "sourceSha256": actual_source_hash,
        "command": command,
        "oleanSha256": sha256_file(output).upper() if output_ok else None,
        "oleanPath": str(output),
        "logSha256": sha256_file(log_path).upper(),
        "logPath": str(log_path),
        "timeSha256": sha256_file(time_path).upper()
        if time_path.is_file() else None,
        "timePath": str(time_path),
        "resultPath": str(result_path),
    }
    result_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
    if not output_ok:
        raise RuntimeError(f"final exact certificate failed: {module}")


def load_final_certificate_results(
        snapshot_id: str, nova_root: Path, runtime: Path,
        tasks: list[dict[str, str]], run_ids: list[str],
        base_ready_hash: str) -> list[dict]:
    for run_id in run_ids:
        if not re.fullmatch(r"final-certificates-\d+", run_id):
            raise RuntimeError(f"invalid final certificate run ID: {run_id}")

    selected: list[dict] = []
    for index, task in enumerate(tasks):
        module = task["module"]
        output = runtime / f"{module}.olean"
        if not output.is_file():
            raise RuntimeError(f"final certificate artifact is missing: {output}")
        output_hash = sha256_file(output).upper()
        accepted = None
        for run_id in reversed(run_ids):
            candidate_root = nova_root / "runs" / run_id
            result_path = (candidate_root /
                           f"{index:02d}-{module}.result.json")
            if not result_path.is_file():
                continue
            result = json.loads(result_path.read_text(encoding="utf-8"))
            log_path = candidate_root / f"{index:02d}-{module}.log"
            time_path = candidate_root / f"{index:02d}-{module}.time.txt"
            artifacts_match = (
                log_path.is_file() and time_path.is_file() and
                result.get("logPath") == str(log_path) and
                result.get("timePath") == str(time_path) and
                result.get("oleanPath") == str(output) and
                result.get("logSha256") == sha256_file(log_path).upper() and
                result.get("timeSha256") == sha256_file(time_path).upper())
            if (artifacts_match and
                    result.get("proofEvidence") is True and
                    result.get("snapshotId") == snapshot_id and
                    result.get("snapshotKind") == "final-proof" and
                    result.get("path2SourceRoot") == FINAL_PATH2_SOURCE_ROOT and
                    result.get("baseReadySha256") == base_ready_hash and
                    result.get("resultPath") == str(result_path) and
                    result.get("taskIndex") == index and
                    result.get("finalTaskCount") == len(tasks) and
                    result.get("exitCode") == 0 and
                    result.get("sourceSha256") == task["sha256"] and
                    result.get("oleanSha256") == output_hash and
                    result.get("task", {}).get("module") == module and
                    result.get("task", {}).get("theorem") == task["theorem"] and
                    result.get("task", {}).get("sha256") == task["sha256"] and
                    result.get("task", {}).get("key") == task["key"]):
                accepted = {
                    "runId": run_id,
                    "resultPath": str(result_path),
                    "resultSha256": sha256_file(result_path).upper(),
                    "result": result,
                }
                break
        if accepted is None:
            raise RuntimeError(
                f"no source-bound successful result matches {module}")
        selected.append(accepted)
    return selected


def finalize(args: argparse.Namespace) -> None:
    snapshot_id = os.environ["BERRY_SNAPSHOT_ID"]
    snapshot_root = Path(os.environ["BERRY_SNAPSHOT_ROOT"])
    build_root = Path(os.environ["BERRY_BUILD_ROOT"])
    build_workspace = build_root / "workspace"
    lean_project = build_workspace / "projects/berry-esseen/lean"
    nova_root = Path(os.environ["BERRY_NOVA_ROOT"])
    ready = build_root / "BASE_READY.json"

    metadata = verify_snapshot(snapshot_root, snapshot_id)
    runtime = path2_source_dir(build_workspace, metadata, require_final=True)
    verify_build_sources(snapshot_root, build_workspace)
    if not ready.is_file():
        raise RuntimeError(f"base build is not ready: {ready}")
    ready_data = json.loads(ready.read_text(encoding="utf-8"))
    verify_base_ready_identity(
        ready_data, snapshot_id, metadata, "finalization")

    tasks = final_certificate_tasks(snapshot_root, metadata)
    verify_final_base_ready_contract(
        ready_data, runtime, tasks, "finalization")
    selected_results = load_final_certificate_results(
        snapshot_id, nova_root, runtime, tasks, args.certificate_run_id,
        sha256_file(ready).upper())
    certificate_modules = {task["module"] for task in tasks}

    roots = FINAL_ROOTS
    order, external = path2_closure(runtime, roots)
    if len(order) != metadata["path2ModuleCount"]:
        raise RuntimeError(
            "computed final closure count does not match snapshot metadata")
    berry_targets = [module for module in external
                     if module.startswith("BerryEsseen.")]
    if berry_targets:
        run(["lake", "build", *berry_targets], cwd=lean_project)

    run_id = os.environ.get(
        "BERRY_RUN_ID", f"finalization-{os.environ.get('SLURM_JOB_ID', 'manual')}")
    run_root = nova_root / "runs" / run_id
    run_root.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    old_lean_path = environment.get("LEAN_PATH", "")
    environment["LEAN_PATH"] = str(runtime) + (
        os.pathsep + old_lean_path if old_lean_path else "")

    module_records: list[dict] = []
    for position, module in enumerate(order):
        source = runtime / f"{module}.lean"
        source_text = source.read_text(encoding="utf-8")
        if module in certificate_modules:
            output = runtime / f"{module}.olean"
            module_records.append({
                "module": module,
                "role": "source-bound native proof root",
                "sourceSha256": sha256_file(source).upper(),
                "oleanSha256": sha256_file(output).upper(),
                "oleanPath": str(output),
            })
            continue
        scan_final_source(source_text, module, native=False)

        output = runtime / f"{module}.olean"
        output.unlink(missing_ok=True)
        stem = f"{position:03d}-{module}"
        log_path = run_root / f"{stem}.log"
        time_path = run_root / f"{stem}.time.txt"
        command = ["/usr/bin/time", "-v", "-o", str(time_path),
                   *lean_command(lean_project, runtime, module, output)]
        started = time.time()
        with log_path.open("w", encoding="utf-8") as log:
            completed = subprocess.run(
                command, cwd=lean_project, env=environment,
                stdout=log, stderr=subprocess.STDOUT)
        finished = time.time()
        record = {
            "module": module,
            "role": "fresh final analytic/assembly elaboration",
            "sourceSha256": sha256_file(source).upper(),
            "exitCode": completed.returncode,
            "elapsedSeconds": finished - started,
            "command": command,
            "oleanSha256": sha256_file(output).upper()
            if completed.returncode == 0 and output.is_file() else None,
            "oleanPath": str(output),
            "logSha256": sha256_file(log_path).upper(),
            "logPath": str(log_path),
            "timeSha256": sha256_file(time_path).upper()
            if time_path.is_file() else None,
            "timePath": str(time_path),
        }
        module_records.append(record)
        if completed.returncode != 0 or not output.is_file():
            failure_path = run_root / "FINALIZATION_FAILED.json"
            failure_path.write_text(
                json.dumps(record, indent=2, sort_keys=True) + "\n",
                encoding="utf-8")
            raise RuntimeError(f"final closure failed at {module}")

    final_audit_module = "Path2Post044TargetAwareConcreteFinalAxiomAudit"
    final_audit_records = [record for record in module_records
                           if record["module"] == final_audit_module]
    if len(final_audit_records) != 1:
        raise RuntimeError("final axiom audit was not elaborated exactly once")
    audit_text = Path(final_audit_records[0]["logPath"]).read_text(
        encoding="utf-8")
    axiom_lists = re.findall(r"\[([^\]]*)\]", audit_text, flags=re.DOTALL)
    if len(axiom_lists) != 1:
        raise RuntimeError(
            f"expected one final axiom list, found {len(axiom_lists)}")
    axioms = [item.strip().strip("'")
              for item in axiom_lists[0].split(",") if item.strip()]
    standard_axioms = ["propext", "Classical.choice", "Quot.sound"]
    native_axioms = [axiom for axiom in axioms
                     if axiom.endswith("._native.native_decide.ax_1_1")]
    unexpected = [axiom for axiom in axioms
                  if axiom not in standard_axioms and
                  not axiom.endswith("._native.native_decide.ax_1_1")]
    if unexpected:
        raise RuntimeError(f"unexpected final axioms: {unexpected!r}")
    for standard in standard_axioms:
        if standard not in axioms:
            raise RuntimeError(f"missing standard final axiom: {standard}")
    if len(native_axioms) != 18:
        raise RuntimeError(
            f"expected 18 native proof-root axioms, got {len(native_axioms)}")
    for task in tasks:
        suffix = task["theorem"] + "._native.native_decide.ax_1_1"
        matching = [axiom for axiom in native_axioms
                    if axiom.endswith(suffix)]
        if len(matching) != 1:
            raise RuntimeError(
                f"expected one native axiom for {task['theorem']}, "
                f"got {matching!r}")
    if len(axioms) != 21 or len(set(axioms)) != 21:
        raise RuntimeError(
            f"expected 21 distinct final axioms, got {axioms!r}")

    final_ready = {
        "purpose": "source-bound final Path 2 theorem and trust audit",
        "proofEvidence": True,
        "snapshotId": snapshot_id,
        "snapshotKind": metadata["snapshotKind"],
        "path2SourceRoot": metadata["path2SourceRoot"],
        "sourceManifestSha256": sha256_file(
            snapshot_root / "source-manifest.tsv").upper(),
        "baseReadySha256": sha256_file(ready).upper(),
        "certificateRunIds": args.certificate_run_id,
        "certificateResults": selected_results,
        "targetConstant": "879/2000",
        "finalTheorem": "BerryEsseen.iidBerryEsseen879_2000_targetAware",
        "finalAxioms": axioms,
        "moduleCount": len(order),
        "moduleRecords": module_records,
        "hostname": socket.gethostname(),
        "slurmJobId": os.environ.get("SLURM_JOB_ID"),
        "finishedAtUnix": time.time(),
    }
    evidence_paths = [ready]
    for selected in selected_results:
        result = selected["result"]
        evidence_paths.extend([
            Path(selected["resultPath"]),
            Path(result["oleanPath"]),
            Path(result["logPath"]),
            Path(result["timePath"]),
        ])
    for record in module_records:
        evidence_paths.append(Path(record["oleanPath"]))
        if "logPath" in record:
            evidence_paths.append(Path(record["logPath"]))
        if "timePath" in record:
            evidence_paths.append(Path(record["timePath"]))
    final_ready, published = publish_final_evidence_bundle(
        nova_root, run_root, evidence_paths, final_ready)
    print(json.dumps({
        "proofEvidence": True,
        "snapshotId": snapshot_id,
        "finalTheorem": final_ready["finalTheorem"],
        "targetConstant": final_ready["targetConstant"],
        "finalAxiomCount": len(axioms),
        "nativeAxiomCount": len(native_axioms),
        "moduleCount": len(order),
        **published,
    }, indent=2, sort_keys=True))


def diagnostic(args: argparse.Namespace) -> None:
    snapshot_id = os.environ["BERRY_SNAPSHOT_ID"]
    snapshot_root = Path(os.environ["BERRY_SNAPSHOT_ROOT"])
    build_root = Path(os.environ["BERRY_BUILD_ROOT"])
    build_workspace = build_root / "workspace"
    lean_project = build_workspace / "projects/berry-esseen/lean"
    metadata = load_snapshot_metadata(snapshot_root, snapshot_id)
    runtime = path2_source_dir(build_workspace, metadata)
    ready = build_root / "BASE_READY.json"
    if not ready.is_file():
        raise RuntimeError(f"base build is not ready: {ready}")

    task_file = (snapshot_root / "workspace" /
                 "projects/berry-esseen/lean/scripts/nova/diagnostic-tasks.tsv")
    task = load_task(task_file, args.index)
    n = int(task["n"])
    fuel = int(task["fuel"])
    module = task["dependency_module"]
    if args.index != n - 1 or not 1 <= n <= 10:
        raise RuntimeError(f"diagnostic task/index mismatch: {task!r}")
    if fuel != 5:
        raise RuntimeError(f"diagnostic fuel must remain 5, got {fuel}")
    if module != "Path2Post044FiniteTargetAwareFailureDiagnostic":
        raise RuntimeError(f"unexpected diagnostic dependency: {module}")

    source = runtime / f"{module}.lean"
    actual_source_hash = sha256_file(source).upper()
    if actual_source_hash != task["sha256"].upper():
        raise RuntimeError(f"pinned source mismatch for {module}")

    array_job_id = os.environ.get("SLURM_ARRAY_JOB_ID", "manual")
    if not re.fullmatch(r"(?:\d+|manual)", array_job_id):
        raise RuntimeError(f"invalid SLURM_ARRAY_JOB_ID: {array_job_id}")
    run_id = os.environ.get(
        "BERRY_RUN_ID", f"finite-diagnostic-{array_job_id}")
    run_root = Path(os.environ["BERRY_NOVA_ROOT"]) / "runs" / run_id
    run_root.mkdir(parents=True, exist_ok=True)
    restart = os.environ.get("SLURM_RESTART_COUNT", "0")
    if not re.fullmatch(r"\d+", restart):
        raise RuntimeError(f"invalid SLURM_RESTART_COUNT: {restart}")
    stem = f"{args.index:02d}-{task['key']}-attempt{restart}"
    # Lean's `-R runtime` requires the input source to be contained in that
    # root.  Keep the generated source in the source-bound build workspace;
    # logs, timing, result JSON, and output object remain in the run record.
    driver_module = (
        f"Path2GeneratedDiagnosticN{n:02d}"
        f"Job{array_job_id.capitalize()}Attempt{restart}"
    )
    driver_path = runtime / f"{driver_module}.lean"
    log_path = run_root / f"{stem}.log"
    time_path = run_root / f"{stem}.time.txt"
    result_path = run_root / f"{stem}.result.json"
    output = run_root / f"{stem}.olean"

    driver_text = (
        "import Path2Post044FiniteTargetAwareFailureDiagnostic\n\n"
        "/- Discovery-only generated driver.  Its output is not proof evidence. -/\n"
        "namespace BerryEsseen\n\n"
        "set_option maxRecDepth 10000\n"
        "set_option maxHeartbeats 0\n\n"
        f"#eval path2Post044FiniteTargetAwareDiagnostic {n} {fuel}\n\n"
        "end BerryEsseen\n"
    )
    with driver_path.open("w", encoding="utf-8", newline="\n") as stream:
        stream.write(driver_text)
    driver_hash = sha256_file(driver_path).upper()
    output.unlink(missing_ok=True)

    environment = os.environ.copy()
    old_lean_path = environment.get("LEAN_PATH", "")
    environment["LEAN_PATH"] = str(runtime) + (
        os.pathsep + old_lean_path if old_lean_path else "")
    command = [
        "/usr/bin/time", "-v", "-o", str(time_path),
        "lake", "env", "lean", "--tstack=32768", "-R", str(runtime),
        "-o", str(output), str(driver_path),
    ]
    started = time.time()
    with log_path.open("w", encoding="utf-8") as log:
        completed = subprocess.run(command, cwd=lean_project, env=environment,
                                   stdout=log, stderr=subprocess.STDOUT)
    finished = time.time()
    log_hash = sha256_file(log_path).upper()

    result = {
        "purpose": "discovery-only exact first-failure diagnostic",
        "proofEvidence": False,
        "snapshotId": snapshot_id,
        "baseReadySha256": sha256_file(ready).upper(),
        "baseReadyPath": str(ready),
        "task": task,
        "taskIndex": args.index,
        "hostname": socket.gethostname(),
        "slurmJobId": os.environ.get("SLURM_JOB_ID"),
        "slurmArrayJobId": os.environ.get("SLURM_ARRAY_JOB_ID"),
        "slurmArrayTaskId": os.environ.get("SLURM_ARRAY_TASK_ID"),
        "slurmRestartCount": restart,
        "startedAtUnix": started,
        "finishedAtUnix": finished,
        "elapsedSeconds": finished - started,
        "exitCode": completed.returncode,
        "dependencySourceSha256": actual_source_hash,
        "driverSourceSha256": driver_hash,
        "driverModule": driver_module,
        "command": command,
        "diagnosticLogSha256": log_hash,
        "oleanSha256": sha256_file(output).upper()
        if completed.returncode == 0 and output.is_file() else None,
        "oleanPath": str(output),
        "driverPath": str(driver_path),
        "logPath": str(log_path),
        "timePath": str(time_path),
        "resultPath": str(result_path),
    }
    result_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
    if completed.returncode != 0 or not output.is_file():
        raise RuntimeError(f"exact diagnostic failed for n={n}")


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    prepare_parser = subparsers.add_parser("prepare")
    prepare_parser.add_argument("--root", action="append", required=True)
    prepare_parser.set_defaults(function=prepare)
    certificate_parser = subparsers.add_parser("certificate")
    certificate_parser.add_argument("--index", type=int, required=True)
    certificate_parser.set_defaults(function=certificate)
    final_certificate_parser = subparsers.add_parser("final-certificate")
    final_certificate_parser.add_argument("--index", type=int, required=True)
    final_certificate_parser.set_defaults(function=final_certificate)
    finalize_parser = subparsers.add_parser("finalize")
    finalize_parser.add_argument(
        "--certificate-run-id", action="append", required=True)
    finalize_parser.set_defaults(function=finalize)
    diagnostic_parser = subparsers.add_parser("diagnostic")
    diagnostic_parser.add_argument("--index", type=int, required=True)
    diagnostic_parser.set_defaults(function=diagnostic)
    args = parser.parse_args()
    args.function(args)


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise
