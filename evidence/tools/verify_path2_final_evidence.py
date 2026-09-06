#!/usr/bin/env python3
"""Fail-closed local acceptance of the final Path 2 Nova evidence.

The finalizer runs on Nova and writes ``FINAL_READY.json``.  This verifier is
deliberately independent of that finalizer: it reconstructs the 79-module
source closure and eighteen native proof roots from an extracted immutable snapshot,
then checks every downloaded result, log, timing record, and ``.olean`` against
the hashes and paths in ``FINAL_READY.json``.  It also independently pins the
Path 1 theorem/interface sources and requires the Path 2 public binders,
assumptions, all-``n`` quantifier, and target constant to differ only in the
intended conclusion constant.

The artifact root must be a local mirror of
``/work/stat-grad/xhn/berry_esseen_path2``.  In particular, a final-ready file
from remote ``runs/finalization-JOB/FINAL_READY.json`` must be supplied as
``ARTIFACT_ROOT/runs/finalization-JOB/FINAL_READY.json``.  Merely possessing a
``FINAL_READY.json`` without its referenced artifacts cannot pass.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import sys
import tempfile
from typing import Any


REMOTE_NOVA_ROOT = PurePosixPath(
    "/work/stat-grad/xhn/berry_esseen_path2")
FINAL_SOURCE_ROOT = "projects/berry-esseen/lean/Path2"
TARGET_CONSTANT = "879/2000"
FINAL_THEOREM = "BerryEsseen.iidBerryEsseen879_2000_targetAware"
FINAL_AUDIT_TARGET = "iidBerryEsseen879_2000_targetAware"
PATH1_CONCRETE_SHA256 = (
    "9903dc4e7ceea25e2edab733f2ef1fdade983559615ff2ed27d51b415c27477b")
PATH1_INTERFACE_SHA256 = (
    "3a4af82eea56aee1b0112be35b5b0321990497358ee02a6092f44115c278ca03")
LEAN_TOOLCHAIN = "leanprover/lean4:v4.29.1"
NOVA_SCRIPT_ROOT = "projects/berry-esseen/lean/scripts/nova"
PINNED_EXECUTION_FILES = (
    "path2_nova.py",
    "path2_finalize.sbatch",
    "path2_final_certificates.sbatch",
    "path2_final_topology.sbatch",
    "prepare_path2_final_base.sbatch",
    "verify_path2_final_evidence.py",
)

FINAL_ROOTS = (
    "Path2Post044TargetAwareConcreteCertificateAxiomAudit",
    "Path2Post044TargetAwareConcreteFinalAxiomAudit",
    "Path2Post044TargetAwareAxiomAudit",
    "Path2Post044InterfaceDominanceAudit",
    "Path2Post044FiniteTargetAwareFuelMonotonicityAxiomAudit",
    "Path2Post044FiniteTargetAwareDiagnosticCorrectnessAxiomAudit",
)

FINAL_PROOF_CONTRACT = {
    "ready": True,
    "sourceRoot": FINAL_SOURCE_ROOT,
    "finiteFirstBatchFuel": 6,
    "finiteLaterBatchFuel": 5,
    "middleFuel": 5,
    "upperFuel": 8,
    "nativeCertificateCount": 18,
    "proofRootCount": 6,
}

EXPECTED_TASK_PAIRS = (
    ("Path2Post044FiniteTargetAwareBatch01_10",
     "path2Post044FiniteTargetAwareBatch01_10_checked"),
    ("Path2Post044FiniteTargetAwareBatch11_20",
     "path2Post044FiniteTargetAwareBatch11_20_checked"),
    ("Path2Post044FiniteTargetAwareBatch21_30",
     "path2Post044FiniteTargetAwareBatch21_30_checked"),
    ("Path2Post044FiniteTargetAwareBatch31_40",
     "path2Post044FiniteTargetAwareBatch31_40_checked"),
    ("Path2Post044FiniteTargetAwareBatch41_50",
     "path2Post044FiniteTargetAwareBatch41_50_checked"),
    ("Path2Post044FiniteTargetAwareBatch51_60",
     "path2Post044FiniteTargetAwareBatch51_60_checked"),
    ("Path2Post044FiniteTargetAwareBatch61_70",
     "path2Post044FiniteTargetAwareBatch61_70_checked"),
    ("Path2Post044FiniteTargetAwareBatch71_80",
     "path2Post044FiniteTargetAwareBatch71_80_checked"),
    ("Path2Post044FiniteTargetAwareBatch81_90",
     "path2Post044FiniteTargetAwareBatch81_90_checked"),
    ("Path2Post044FiniteTargetAwareBatch91_99",
     "path2Post044FiniteTargetAwareBatch91_99_checked"),
    ("Path2VariableAlphaSmallLowerNativeCheck",
     "path2VariableAlphaSmallLowerConcreteCertificate_checked"),
    ("Path2VariableAlphaSmallUpperNativeCheck",
     "path2VariableAlphaSmallUpperConcreteCertificate_checked"),
    ("Path2Post044LargeMiddleFuel5ShardBatch01NativeCheck",
     "Path2Post044LargeMiddleFuel5ShardBatch01NativeCheckCertificate_checked"),
    ("Path2Post044LargeMiddleFuel5ShardBatch02NativeCheck",
     "Path2Post044LargeMiddleFuel5ShardBatch02NativeCheckCertificate_checked"),
    ("Path2Post044LargeMiddleFuel5ShardBatch03NativeCheck",
     "Path2Post044LargeMiddleFuel5ShardBatch03NativeCheckCertificate_checked"),
    ("Path2Post044LargeMiddleFuel5ShardBatch04NativeCheck",
     "Path2Post044LargeMiddleFuel5ShardBatch04NativeCheckCertificate_checked"),
    ("Path2Post044LargeUpperFuel8NativeCheck",
     "path2Post044LargeUpperFuel8ConcreteCertificate_checked"),
    ("Path2Post044LargeMiddleFuel5ShardedComposition",
     "path2Post044LargeMiddleFuel5ShardedFullCodeParsed"),
)

SNAPSHOT_KEYS = {
    "schemaVersion", "snapshotId", "generatedAtUtc", "snapshotKind",
    "targetConstant", "leanToolchain", "roots", "path2SourceRoot",
    "path2ModuleCount", "fileCount", "sourceManifestSha256",
    "finalProofSnapshot",
}
FINAL_READY_KEYS = {
    "purpose", "proofEvidence", "snapshotId", "snapshotKind",
    "path2SourceRoot", "sourceManifestSha256", "baseReadySha256",
    "certificateRunIds", "certificateResults", "targetConstant",
    "finalTheorem", "finalAxioms", "moduleCount", "moduleRecords",
    "hostname", "slurmJobId", "finishedAtUnix", "evidenceManifestPath",
    "evidenceManifestSha256", "evidenceArtifactCount",
}
BASE_READY_KEYS = {
    "snapshotId", "preparedAtUnix", "hostname", "roots", "snapshotKind",
    "path2SourceRoot", "seedBuildId", "path2DependencyCount",
    "externalImports", "leanVersion", "lakeVersion",
}
SELECTED_RESULT_KEYS = {"runId", "resultPath", "resultSha256", "result"}
CERTIFICATE_RESULT_KEYS = {
    "purpose", "proofEvidence", "evidenceScope", "snapshotId",
    "snapshotKind", "path2SourceRoot", "baseReadySha256", "baseReadyPath",
    "task", "taskIndex", "finalTaskCount", "hostname", "slurmJobId",
    "slurmArrayJobId", "slurmArrayTaskId", "startedAtUnix",
    "finishedAtUnix", "elapsedSeconds", "exitCode", "sourceSha256",
    "command", "oleanSha256", "oleanPath", "logSha256", "logPath",
    "timeSha256", "timePath", "resultPath",
}
NATIVE_RECORD_KEYS = {
    "module", "role", "sourceSha256", "oleanSha256", "oleanPath",
}
ANALYTIC_RECORD_KEYS = {
    "module", "role", "sourceSha256", "exitCode", "elapsedSeconds",
    "command", "oleanSha256", "oleanPath", "logSha256", "logPath",
    "timeSha256", "timePath",
}

IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*$")
AXIOM_PRINT_RE = re.compile(r"^\s*#print\s+axioms\s+(\S+)\s*$")
FORBIDDEN_SOURCE_TOKENS = ("axiom", "opaque", "unsafe", "sorry", "admit")
SOURCE_TOKEN_BOUNDARY = r"[A-Za-z0-9_']"
SHA256_RE = re.compile(r"[0-9A-Fa-f]{64}\Z")
COMPUTE_HOST_RE = re.compile(r"nova[0-9]+-[0-9]+\Z")
CANONICAL_JOB_RE = re.compile(r"[1-9][0-9]*\Z")
CERTIFICATE_RUN_RE = re.compile(r"final-certificates-([1-9][0-9]*)\Z")
FINALIZATION_RUN_RE = re.compile(r"finalization-([1-9][0-9]*)\Z")


class AuditFailure(RuntimeError):
    """A fail-closed contract violation."""


@dataclass(frozen=True)
class Task:
    key: str
    module: str
    theorem: str
    sha256: str

    def as_dict(self) -> dict[str, str]:
        return {
            "key": self.key,
            "module": self.module,
            "theorem": self.theorem,
            "sha256": self.sha256,
        }


@dataclass(frozen=True)
class SnapshotAudit:
    snapshot_id: str
    metadata: dict[str, Any]
    runtime: Path
    manifest_records: dict[str, tuple[str, int]]
    order: tuple[str, ...]
    external_imports: tuple[str, ...]
    tasks: tuple[Task, ...]
    source_hashes: dict[str, str]
    interface_audit: dict[str, Any]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditFailure(message)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require_sha256(value: Any, field: str) -> str:
    require(type(value) is str and SHA256_RE.fullmatch(value) is not None,
            f"{field}: expected 64 hexadecimal digits")
    return value.upper()


def require_exact_keys(value: dict[str, Any], expected: set[str],
                       field: str) -> None:
    actual = set(value)
    require(actual == expected,
            f"{field}: exact schema mismatch; "
            f"missing={sorted(expected - actual)}, "
            f"unexpected={sorted(actual - expected)}")


def require_exact_int(value: Any, expected: int, field: str) -> None:
    require(type(value) is int and value == expected,
            f"{field}: expected exact integer {expected}")


def finite_number(value: Any, field: str, *, positive: bool = False) -> float:
    require(type(value) in (int, float) and math.isfinite(float(value)),
            f"{field}: expected a finite JSON number")
    converted = float(value)
    require(converted > 0 if positive else converted >= 0,
            f"{field}: expected {'positive' if positive else 'nonnegative'} value")
    return converted


def read_json_object(path: Path, field: str) -> dict[str, Any]:
    require(path.is_file(), f"{field}: missing file {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8-sig"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise AuditFailure(f"{field}: cannot read JSON: {error}") from error
    require(type(value) is dict, f"{field}: expected a JSON object")
    return value


def safe_manifest_relative(value: str, field: str) -> PurePosixPath:
    require(type(value) is str and value != "" and "\\" not in value,
            f"{field}: invalid manifest path")
    relative = PurePosixPath(value)
    require(not relative.is_absolute() and ".." not in relative.parts and
            "." not in relative.parts and relative.as_posix() == value,
            f"{field}: unsafe or noncanonical manifest path {value!r}")
    return relative


def parse_manifest(path: Path) -> dict[str, tuple[str, int]]:
    require(path.is_file(), f"snapshot manifest: missing file {path}")
    records: dict[str, tuple[str, int]] = {}
    try:
        lines = path.read_text(encoding="utf-8-sig").splitlines()
    except (OSError, UnicodeError) as error:
        raise AuditFailure(f"snapshot manifest: cannot read: {error}") from error
    require(lines, "snapshot manifest: empty file")
    for line_number, line in enumerate(lines, start=1):
        parts = line.split("\t")
        require(len(parts) == 3,
                f"snapshot manifest:{line_number}: expected three columns")
        relative, digest, byte_count = parts
        safe_manifest_relative(relative,
                               f"snapshot manifest:{line_number}.path")
        require(relative not in records,
                f"snapshot manifest:{line_number}: duplicate path {relative}")
        require(re.fullmatch(r"0|[1-9][0-9]*", byte_count) is not None,
                f"snapshot manifest:{line_number}: noncanonical byte count")
        records[relative] = (
            require_sha256(
                digest, f"snapshot manifest:{line_number}.sha256"),
            int(byte_count),
        )
    return records


def parse_imports(path: Path) -> list[str]:
    imports: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            imports.extend(match.group(1).split())
    return imports


def path2_closure(runtime: Path, roots: list[str] | tuple[str, ...]
                  ) -> tuple[list[str], list[str]]:
    visited: set[str] = set()
    visiting: set[str] = set()
    order: list[str] = []
    external: set[str] = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        require(module not in visiting, f"Path 2 import cycle at {module}")
        visiting.add(module)
        source = runtime / f"{module}.lean"
        require(source.is_file(), f"missing Path 2 source: {source}")
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
    require(block_depth == 0,
            f"unterminated Lean block comment in {module}")
    require(not in_string, f"unterminated Lean string in {module}")
    return "".join(output)


def source_token_matches(source: str, token: str) -> list[re.Match[str]]:
    return list(re.finditer(
        rf"(?<!{SOURCE_TOKEN_BOUNDARY}){re.escape(token)}"
        rf"(?!{SOURCE_TOKEN_BOUNDARY})", source))


def source_line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def scan_source(source: Path, module: str, *, native: bool) -> None:
    text = source.read_text(encoding="utf-8")
    code = strip_lean_comments_and_strings(text, module)
    for token in FORBIDDEN_SOURCE_TOKENS:
        matches = source_token_matches(code, token)
        require(not matches,
                f"forbidden source token {token!r} in {module} at line "
                f"{source_line_number(code, matches[0].start())}"
                if matches else "")
    native_count = len(source_token_matches(code, "native_decide"))
    expected = 1 if native else 0
    require(native_count == expected,
            f"{module}: expected {expected} native_decide tokens, "
            f"found {native_count}")


def normalized_whitespace(text: str) -> str:
    return re.sub(r"\s+", " ", text)


def unique_match(pattern: str, text: str, field: str) -> re.Match[str]:
    matches = list(re.finditer(pattern, text))
    require(len(matches) == 1,
            f"{field}: expected one source match, found {len(matches)}")
    return matches[0]


def verify_path1_public_interface(
        workspace: Path, runtime: Path,
        records: dict[str, tuple[str, int]]) -> dict[str, Any]:
    """Pin Path 1 and require exact public/all-n Path 2 interface equality."""
    path1_root = workspace / "projects" / "berry-esseen" / "lean" / "BerryEsseen"
    paths = {
        "path1Concrete": path1_root / "PrawitzConcreteNumericalCertificate.lean",
        "path1Interface": path1_root / "Interface.lean",
        "path2Concrete": runtime /
            "Path2Post044TargetAwareConcreteFinalTheorem.lean",
        "path2Conclusion": runtime / "Path2Post044UniversalSplitPrototype.lean",
    }
    for field, path in paths.items():
        require(path.is_file(), f"{field}: required interface source is missing")
        relative = path.relative_to(workspace).as_posix()
        require(relative in records,
                f"{field}: interface source is absent from the snapshot manifest")

    hashes = {field: sha256_file(path) for field, path in paths.items()}
    require(hashes["path1Concrete"] == PATH1_CONCRETE_SHA256,
            "snapshot Path 1 concrete theorem source differs from the pinned baseline")
    require(hashes["path1Interface"] == PATH1_INTERFACE_SHA256,
            "snapshot Path 1 interface source differs from the pinned baseline")

    texts = {
        field: path.read_text(encoding="utf-8")
        for field, path in paths.items()
    }
    path1_theorem = unique_match(
        r"(?s)theorem\s+iidBerryEsseen45(?P<body>.*?)\s*:=",
        texts["path1Concrete"],
        "Path 1 public theorem",
    )
    path2_theorem = unique_match(
        r"(?s)theorem\s+iidBerryEsseen879_2000_targetAware(?P<body>.*?)\s*:=",
        texts["path2Concrete"],
        "Path 2 public theorem",
    )
    path1_signature = normalized_whitespace(
        path1_theorem.group("body")).strip()
    path2_signature = normalized_whitespace(
        path2_theorem.group("body").replace(
            "IIDBerryEsseen879_2000Conclusion",
            "IIDBerryEsseen45Conclusion",
        )).strip()
    require(path2_signature == path1_signature,
            "Path 2 public theorem binders or assumptions differ from Path 1")

    path1_conclusion = unique_match(
        r"(?s)def\s+IIDBerryEsseen45Conclusion(?P<body>.*?)(?=\r?\n\r?\ntheorem\s)",
        texts["path1Interface"],
        "Path 1 all-n conclusion",
    )
    path2_conclusion = unique_match(
        r"(?s)def\s+IIDBerryEsseen879_2000Conclusion(?P<body>.*?)(?=\r?\n\r?\ntheorem\s)",
        texts["path2Conclusion"],
        "Path 2 all-n conclusion",
    )
    path1_all_n = normalized_whitespace(
        path1_conclusion.group("body").replace(
            "targetConstant", "TARGET")).strip()
    path2_all_n = normalized_whitespace(
        path2_conclusion.group("body").replace(
            "path2Post044TargetConstant", "TARGET")).strip()
    require(path2_all_n == path1_all_n,
            "Path 2 conclusion changes the Path 1 all-n interface")
    unique_match(
        r"(?m)^[ \t]*def[ \t]+path2Post044TargetConstant[ \t]*:[ \t]*"
        r"ℝ[ \t]*:=[ \t]*\(879[ \t]*:[ \t]*ℝ\)[ \t]*/[ \t]*2000[ \t]*$",
        texts["path2Conclusion"],
        "Path 2 target 879/2000 definition",
    )
    return {
        "publicTheoremInterfaceMatchesPath1": True,
        "allNConclusionInterfaceMatchesPath1": True,
        "targetConstantMatches879Over2000": True,
        "sourceSha256": {field: digest.upper()
                         for field, digest in hashes.items()},
    }


def derive_tasks(runtime: Path) -> tuple[Task, ...]:
    audit = runtime / (
        "Path2Post044TargetAwareConcreteCertificateAxiomAudit.lean")
    require(audit.is_file(), "final certificate axiom-audit source is missing")
    modules = [item for item in parse_imports(audit)
               if item.startswith("Path2")]
    theorems: list[str] = []
    for line in audit.read_text(encoding="utf-8").splitlines():
        match = AXIOM_PRINT_RE.match(line)
        if match:
            theorems.append(match.group(1))
    actual_pairs = tuple(zip(modules, theorems))
    require(actual_pairs == EXPECTED_TASK_PAIRS,
            "final certificate audit does not contain the exact ordered "
            "eighteen-task native-root set")

    tasks: list[Task] = []
    for index, (module, theorem) in enumerate(EXPECTED_TASK_PAIRS):
        source = runtime / f"{module}.lean"
        require(source.is_file(), f"native certificate source missing: {module}")
        scan_source(source, module, native=True)
        text = source.read_text(encoding="utf-8")
        require(re.search(
            rf"\btheorem\s+{re.escape(theorem)}\s*:", text) is not None,
            f"{module}: expected theorem declaration {theorem}")
        tasks.append(Task(
            key=f"final-{index:02d}",
            module=module,
            theorem=theorem,
            sha256=sha256_file(source).upper(),
        ))
    return tuple(tasks)


def verify_final_target_sources(runtime: Path) -> None:
    audit = runtime / "Path2Post044TargetAwareConcreteFinalAxiomAudit.lean"
    require(audit.is_file(), "final theorem axiom-audit source is missing")
    require(parse_imports(audit) == [
        "Path2Post044TargetAwareConcreteFinalTheorem"],
        "final theorem axiom audit imports the wrong module")
    targets = []
    for line in audit.read_text(encoding="utf-8").splitlines():
        match = AXIOM_PRINT_RE.match(line)
        if match:
            targets.append(match.group(1))
    require(targets == [FINAL_AUDIT_TARGET],
            "final theorem axiom audit prints the wrong target")

    theorem_source = runtime / (
        "Path2Post044TargetAwareConcreteFinalTheorem.lean")
    theorem_text = theorem_source.read_text(encoding="utf-8")
    require(re.search(
        rf"\btheorem\s+{re.escape(FINAL_AUDIT_TARGET)}\b", theorem_text)
        is not None,
        "final theorem source does not declare the target theorem")


def audit_path2_source_root(
        runtime: Path
        ) -> tuple[tuple[str, ...], tuple[str, ...], tuple[Task, ...],
                   dict[str, str]]:
    """Audit one complete durable Path 2 source root before any build."""
    runtime = runtime.resolve()
    require(runtime.is_dir(), "durable Path 2 source root is missing")
    order, external = path2_closure(runtime, FINAL_ROOTS)
    require(len(order) == 79 and len(set(order)) == 79,
            "final source closure is not exactly 79 distinct modules")
    actual_sources = {path.stem for path in runtime.glob("*.lean")}
    require(actual_sources == set(order),
            "durable Path 2 directory differs from the final 79-module closure")

    tasks = derive_tasks(runtime)
    certificate_modules = {task.module for task in tasks}
    for module in order:
        if module not in certificate_modules:
            scan_source(runtime / f"{module}.lean", module, native=False)
    verify_final_target_sources(runtime)
    source_hashes = {
        module: sha256_file(runtime / f"{module}.lean").upper()
        for module in order
    }
    return (tuple(order), tuple(external), tasks, source_hashes)


def audit_snapshot(snapshot_root: Path) -> SnapshotAudit:
    snapshot_root = snapshot_root.resolve()
    metadata = read_json_object(snapshot_root / "snapshot.json",
                                "snapshot metadata")
    require_exact_keys(metadata, SNAPSHOT_KEYS, "snapshot metadata")
    require_exact_int(metadata.get("schemaVersion"), 2,
                      "snapshot.schemaVersion")
    require(type(metadata.get("generatedAtUtc")) is str and
            metadata["generatedAtUtc"] != "", "snapshot.generatedAtUtc")
    require(metadata.get("snapshotKind") == "final-proof",
            "snapshot kind must be final-proof")
    require(metadata.get("targetConstant") == TARGET_CONSTANT,
            "snapshot target constant mismatch")
    require(metadata.get("leanToolchain") == LEAN_TOOLCHAIN,
            "snapshot Lean toolchain mismatch")
    require(metadata.get("roots") == list(FINAL_ROOTS),
            "snapshot proof roots mismatch")
    require(metadata.get("path2SourceRoot") == FINAL_SOURCE_ROOT,
            "snapshot Path 2 source root mismatch")
    require_exact_int(metadata.get("path2ModuleCount"), 79,
                      "snapshot.path2ModuleCount")
    require(type(metadata.get("finalProofSnapshot")) is dict and
            metadata["finalProofSnapshot"] == FINAL_PROOF_CONTRACT,
            "snapshot final-proof wiring contract mismatch")

    manifest_path = snapshot_root / "source-manifest.tsv"
    snapshot_id = sha256_file(manifest_path)
    require(type(metadata.get("snapshotId")) is str and
            metadata["snapshotId"] == snapshot_id,
            "snapshot ID does not equal the manifest SHA-256")
    require(metadata.get("sourceManifestSha256") == snapshot_id,
            "snapshot manifest identity field mismatch")
    records = parse_manifest(manifest_path)
    require_exact_int(metadata.get("fileCount"), len(records),
                      "snapshot.fileCount")

    workspace = snapshot_root / "workspace"
    require(workspace.is_dir(), "snapshot workspace is missing")
    workspace_resolved = workspace.resolve()
    for relative, (expected_hash, expected_size) in records.items():
        path = workspace.joinpath(*PurePosixPath(relative).parts)
        require(path.is_file(), f"snapshot file missing: {relative}")
        try:
            path.resolve().relative_to(workspace_resolved)
        except ValueError as error:
            raise AuditFailure(
                f"snapshot file escapes workspace: {relative}") from error
        require(path.stat().st_size == expected_size,
                f"snapshot size mismatch: {relative}")
        require(sha256_file(path).upper() == expected_hash,
                f"snapshot SHA-256 mismatch: {relative}")

    local_script_root = Path(__file__).resolve().parent
    for filename in PINNED_EXECUTION_FILES:
        relative = f"{NOVA_SCRIPT_ROOT}/{filename}"
        require(relative in records,
                f"snapshot omits proof execution file: {relative}")
        snapshot_script = workspace.joinpath(*PurePosixPath(relative).parts)
        local_script = local_script_root / filename
        require(local_script.is_file(),
                f"local reviewed execution file is missing: {local_script}")
        require(sha256_file(local_script).upper() == records[relative][0] and
                local_script.stat().st_size == records[relative][1],
                f"local execution file differs from immutable snapshot: "
                f"{filename}")

    runtime = workspace.joinpath(*PurePosixPath(FINAL_SOURCE_ROOT).parts)
    order, external, tasks, source_hashes = audit_path2_source_root(runtime)
    for module in order:
        source = runtime / f"{module}.lean"
        relative = source.relative_to(workspace).as_posix()
        require(relative in records,
                f"final closure source absent from manifest: {module}")
    interface_audit = verify_path1_public_interface(
        workspace, runtime, records)
    return SnapshotAudit(
        snapshot_id=snapshot_id,
        metadata=metadata,
        runtime=runtime,
        manifest_records=records,
        order=tuple(order),
        external_imports=tuple(external),
        tasks=tasks,
        source_hashes=source_hashes,
        interface_audit=interface_audit,
    )


def local_for_remote(remote_value: Any, artifact_root: Path,
                     field: str) -> Path:
    require(type(remote_value) is str, f"{field}: expected a remote path")
    remote = PurePosixPath(remote_value)
    require(remote.is_absolute(), f"{field}: remote path is not absolute")
    try:
        relative = remote.relative_to(REMOTE_NOVA_ROOT)
    except ValueError as error:
        raise AuditFailure(
            f"{field}: remote path is outside {REMOTE_NOVA_ROOT}") from error
    require(".." not in relative.parts and "." not in relative.parts,
            f"{field}: unsafe remote path")
    local = artifact_root.joinpath(*relative.parts)
    require(local.is_file(), f"{field}: downloaded artifact missing: {local}")
    try:
        local.resolve().relative_to(artifact_root.resolve())
    except ValueError as error:
        raise AuditFailure(f"{field}: local artifact escapes mirror") from error
    return local


def expected_build_paths(snapshot_id: str, module: str) -> tuple[str, str]:
    runtime = (REMOTE_NOVA_ROOT / "builds" / snapshot_id / "workspace" /
               PurePosixPath(FINAL_SOURCE_ROOT))
    return str(runtime / f"{module}.lean"), str(runtime / f"{module}.olean")


def expected_lean_command(snapshot_id: str, module: str, time_path: str,
                          olean_path: str) -> list[str]:
    source_path, expected_olean = expected_build_paths(snapshot_id, module)
    require(olean_path == expected_olean,
            f"{module}: unexpected .olean path")
    runtime = str(PurePosixPath(source_path).parent)
    return [
        "/usr/bin/time", "-v", "-o", time_path,
        "lake", "env", "lean", "--tstack=32768", "-R", runtime,
        "-o", olean_path, source_path,
    ]


def audit_hashed_artifact(remote_path: Any, expected_hash: Any,
                          artifact_root: Path, field: str,
                          *, nonempty: bool = False) -> Path:
    local = local_for_remote(remote_path, artifact_root, field)
    digest = require_sha256(expected_hash, field + ".sha256")
    require(sha256_file(local).upper() == digest,
            f"{field}: downloaded SHA-256 mismatch")
    if nonempty:
        require(local.stat().st_size > 0, f"{field}: empty artifact")
    return local


def remote_relative(value: Any, field: str) -> str:
    require(type(value) is str, f"{field}: expected a remote path")
    path = PurePosixPath(value)
    try:
        relative = path.relative_to(REMOTE_NOVA_ROOT)
    except ValueError as error:
        raise AuditFailure(
            f"{field}: remote path is outside {REMOTE_NOVA_ROOT}") from error
    require(path.is_absolute() and ".." not in relative.parts and
            "." not in relative.parts,
            f"{field}: unsafe remote path")
    return relative.as_posix()


def expected_evidence_inventory(final_ready: dict[str, Any]) -> set[str]:
    paths: list[tuple[Any, str]] = []
    selected = final_ready.get("certificateResults")
    require(type(selected) is list,
            "FINAL_READY certificate results are not a list")
    for index, wrapper in enumerate(selected):
        require(type(wrapper) is dict,
                f"certificateResults[{index}]: expected object")
        result = wrapper.get("result")
        require(type(result) is dict,
                f"certificateResults[{index}].result: expected object")
        paths.append((wrapper.get("resultPath"),
                      f"certificateResults[{index}].resultPath"))
        for key in ("oleanPath", "logPath", "timePath"):
            paths.append((result.get(key),
                          f"certificateResults[{index}].result.{key}"))
    records = final_ready.get("moduleRecords")
    require(type(records) is list, "FINAL_READY module records are not a list")
    for index, record in enumerate(records):
        require(type(record) is dict,
                f"moduleRecords[{index}]: expected object")
        paths.append((record.get("oleanPath"),
                      f"moduleRecords[{index}].oleanPath"))
        if "logPath" in record:
            paths.append((record.get("logPath"),
                          f"moduleRecords[{index}].logPath"))
        if "timePath" in record:
            paths.append((record.get("timePath"),
                          f"moduleRecords[{index}].timePath"))
    certificate_results = selected
    require(certificate_results and
            type(certificate_results[0].get("result")) is dict,
            "cannot derive BASE_READY path from certificate results")
    paths.append((certificate_results[0]["result"].get("baseReadyPath"),
                  "certificateResults[0].result.baseReadyPath"))
    inventory = {remote_relative(value, field) for value, field in paths}
    require(len(inventory) == 256,
            f"expected 256 distinct evidence artifacts, got {len(inventory)}")
    return inventory


def audit_evidence_manifest(final_ready: dict[str, Any], artifact_root: Path,
                            final_run_remote: PurePosixPath
                            ) -> dict[str, Any]:
    expected_path = str(final_run_remote / "FINAL_EVIDENCE_MANIFEST.tsv")
    require(final_ready.get("evidenceManifestPath") == expected_path,
            "FINAL_READY evidence manifest path mismatch")
    local = audit_hashed_artifact(
        expected_path, final_ready.get("evidenceManifestSha256"),
        artifact_root, "final evidence manifest", nonempty=True)
    records = parse_manifest(local)
    require_exact_int(final_ready.get("evidenceArtifactCount"), 256,
                      "FINAL_READY.evidenceArtifactCount")
    require(len(records) == 256,
            f"evidence manifest must contain 256 entries, got {len(records)}")
    expected = expected_evidence_inventory(final_ready)
    require(set(records) == expected,
            "evidence manifest does not exactly match FINAL_READY artifacts")
    for relative, (digest, byte_count) in records.items():
        remote = str(REMOTE_NOVA_ROOT / PurePosixPath(relative))
        artifact = local_for_remote(
            remote, artifact_root, f"evidence manifest entry {relative}")
        require(artifact.stat().st_size == byte_count,
                f"evidence manifest size mismatch: {relative}")
        require(sha256_file(artifact).upper() == digest,
                f"evidence manifest SHA-256 mismatch: {relative}")
    return {
        "path": expected_path,
        "sha256": sha256_file(local).upper(),
        "artifactCount": len(records),
    }


def audit_base_ready(snapshot: SnapshotAudit, final_ready: dict[str, Any],
                     base_ready_path: str, artifact_root: Path) -> dict[str, Any]:
    expected_remote = str(
        REMOTE_NOVA_ROOT / "builds" / snapshot.snapshot_id /
        "BASE_READY.json")
    require(base_ready_path == expected_remote,
            "BASE_READY path does not belong to the final snapshot build")
    local = audit_hashed_artifact(
        base_ready_path, final_ready.get("baseReadySha256"), artifact_root,
        "BASE_READY", nonempty=True)
    ready = read_json_object(local, "BASE_READY")
    require_exact_keys(ready, BASE_READY_KEYS, "BASE_READY")
    require(ready.get("snapshotId") == snapshot.snapshot_id,
            "BASE_READY snapshot ID mismatch")
    require(ready.get("snapshotKind") == "final-proof" and
            ready.get("path2SourceRoot") == FINAL_SOURCE_ROOT,
            "BASE_READY final source identity mismatch")
    roots = [task.module for task in snapshot.tasks]
    require(ready.get("roots") == roots,
            "BASE_READY roots are not the eighteen native proof roots")
    closure, external = path2_closure(snapshot.runtime, roots)
    dependency_count = len(closure) - len(roots)
    require(dependency_count == 44,
            f"final base dependency closure changed from 44 to {dependency_count}")
    require_exact_int(ready.get("path2DependencyCount"), dependency_count,
                      "BASE_READY.path2DependencyCount")
    require(ready.get("externalImports") == external,
            "BASE_READY external imports mismatch")
    finite_number(ready.get("preparedAtUnix"), "BASE_READY.preparedAtUnix",
                  positive=True)
    require(type(ready.get("hostname")) is str and
            COMPUTE_HOST_RE.fullmatch(ready["hostname"]) is not None,
            "BASE_READY hostname is not a Nova compute node")
    seed = ready.get("seedBuildId")
    require(seed is None or
            (type(seed) is str and re.fullmatch(r"[0-9a-f]{64}", seed)),
            "BASE_READY seedBuildId is invalid")
    require(type(ready.get("leanVersion")) is str and
            re.match(r"^Lean \(version 4\.29\.1(?:,|\))",
                     ready["leanVersion"]) is not None,
            "BASE_READY Lean version mismatch")
    require(type(ready.get("lakeVersion")) is str and
            ready["lakeVersion"] != "", "BASE_READY Lake version missing")
    return {
        "sha256": sha256_file(local).upper(),
        "hostname": ready["hostname"],
        "dependencyCount": dependency_count,
        "leanVersion": ready["leanVersion"],
        "lakeVersion": ready["lakeVersion"],
    }


def require_timing(result: dict[str, Any], field: str) -> None:
    started = finite_number(result.get("startedAtUnix"),
                            field + ".startedAtUnix", positive=True)
    finished = finite_number(result.get("finishedAtUnix"),
                             field + ".finishedAtUnix", positive=True)
    elapsed = finite_number(result.get("elapsedSeconds"),
                            field + ".elapsedSeconds")
    require(finished >= started and
            math.isclose(elapsed, finished - started,
                         rel_tol=0.0, abs_tol=1e-6),
            f"{field}: inconsistent timing metadata")


def audit_certificate_results(
        snapshot: SnapshotAudit, final_ready: dict[str, Any],
        artifact_root: Path) -> tuple[list[dict[str, Any]], str]:
    run_ids = final_ready.get("certificateRunIds")
    require(type(run_ids) is list and len(run_ids) >= 1 and
            all(type(item) is str and CERTIFICATE_RUN_RE.fullmatch(item)
                for item in run_ids) and len(set(run_ids)) == len(run_ids),
            "FINAL_READY certificate run IDs are invalid or duplicated")
    selected = final_ready.get("certificateResults")
    require(type(selected) is list and len(selected) == 18,
            "FINAL_READY must contain exactly eighteen native-root results")

    base_paths: set[str] = set()
    accepted: list[dict[str, Any]] = []
    for index, (wrapper, task) in enumerate(zip(selected, snapshot.tasks)):
        field = f"certificateResults[{index}]"
        require(type(wrapper) is dict, f"{field}: expected object")
        require_exact_keys(wrapper, SELECTED_RESULT_KEYS, field)
        run_id = wrapper.get("runId")
        require(type(run_id) is str and run_id in run_ids,
                f"{field}: selected run ID was not authorized")
        run_match = CERTIFICATE_RUN_RE.fullmatch(run_id)
        require(run_match is not None, f"{field}: invalid selected run ID")
        result = wrapper.get("result")
        require(type(result) is dict, f"{field}.result: expected object")
        require_exact_keys(result, CERTIFICATE_RESULT_KEYS,
                           f"{field}.result")

        stem = f"{index:02d}-{task.module}"
        remote_run = REMOTE_NOVA_ROOT / "runs" / run_id
        expected_result = str(remote_run / f"{stem}.result.json")
        expected_log = str(remote_run / f"{stem}.log")
        expected_time = str(remote_run / f"{stem}.time.txt")
        _, expected_olean = expected_build_paths(
            snapshot.snapshot_id, task.module)
        require(wrapper.get("resultPath") == expected_result and
                result.get("resultPath") == expected_result,
                f"{field}: result path mismatch")
        result_local = audit_hashed_artifact(
            expected_result, wrapper.get("resultSha256"), artifact_root,
            f"{field}.resultFile", nonempty=True)
        actual_result = read_json_object(result_local, f"{field}.resultFile")
        require(actual_result == result,
                f"{field}: embedded result differs from downloaded JSON")

        exact_values = {
            "purpose": "final source-bound native proof root",
            "proofEvidence": True,
            "evidenceScope": (
                "one native proof root; final concrete assembly and "
                "trust audit remain required"),
            "snapshotId": snapshot.snapshot_id,
            "snapshotKind": "final-proof",
            "path2SourceRoot": FINAL_SOURCE_ROOT,
            "baseReadySha256": final_ready["baseReadySha256"],
            "taskIndex": index,
            "finalTaskCount": 18,
            "exitCode": 0,
            "sourceSha256": task.sha256,
            "oleanPath": expected_olean,
            "logPath": expected_log,
            "timePath": expected_time,
            "resultPath": expected_result,
        }
        for key, expected in exact_values.items():
            actual = result.get(key)
            if type(expected) in (bool, int):
                require(type(actual) is type(expected) and actual == expected,
                        f"{field}.{key}: expected {expected!r}")
            else:
                require(actual == expected,
                        f"{field}.{key}: expected {expected!r}")
        require(result.get("task") == task.as_dict(),
                f"{field}: source-bound task mismatch")
        require(type(result.get("hostname")) is str and
                COMPUTE_HOST_RE.fullmatch(result["hostname"]) is not None,
                f"{field}: hostname is not a Nova compute node")
        if index < 17:
            require(type(result.get("slurmArrayJobId")) is str and
                    result["slurmArrayJobId"] == run_match.group(1),
                    f"{field}: array job ID does not match run ID")
            require(type(result.get("slurmArrayTaskId")) is str and
                    result["slurmArrayTaskId"] == str(index),
                    f"{field}: array task ID mismatch")
        else:
            require(result.get("slurmArrayJobId") is None and
                    result.get("slurmArrayTaskId") is None,
                    f"{field}: topology root must come from the dependent scalar job")
        require(type(result.get("slurmJobId")) is str and
                re.fullmatch(r"[1-9][0-9]*(?:_[0-9]+)?",
                             result["slurmJobId"]) is not None,
                f"{field}: invalid Slurm job ID")
        require_timing(result, field)

        base_path = result.get("baseReadyPath")
        require(type(base_path) is str, f"{field}: missing BASE_READY path")
        base_paths.add(base_path)
        require(result.get("command") == expected_lean_command(
            snapshot.snapshot_id, task.module, expected_time, expected_olean),
            f"{field}: Lean command mismatch")
        olean_local = audit_hashed_artifact(
            expected_olean, result.get("oleanSha256"), artifact_root,
            f"{field}.olean", nonempty=True)
        audit_hashed_artifact(
            expected_log, result.get("logSha256"), artifact_root,
            f"{field}.log")
        audit_hashed_artifact(
            expected_time, result.get("timeSha256"), artifact_root,
            f"{field}.time", nonempty=True)
        accepted.append({
            "index": index,
            "module": task.module,
            "theorem": task.theorem,
            "runId": run_id,
            "resultSha256": sha256_file(result_local).upper(),
            "oleanSha256": sha256_file(olean_local).upper(),
            "hostname": result["hostname"],
            "elapsedSeconds": result["elapsedSeconds"],
        })
    require(len(base_paths) == 1,
            "certificate results do not share one exact BASE_READY artifact")
    return accepted, next(iter(base_paths))


def parse_axiom_log(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    axiom_lists = re.findall(r"\[([^\]]*)\]", text, flags=re.DOTALL)
    require(len(axiom_lists) == 1,
            f"final axiom log: expected one list, found {len(axiom_lists)}")
    return [item.strip().strip("'") for item in axiom_lists[0].split(",")
            if item.strip()]


def audit_axioms(axioms_value: Any,
                 tasks: tuple[Task, ...]) -> list[str]:
    require(type(axioms_value) is list and
            all(type(item) is str for item in axioms_value),
            "FINAL_READY.finalAxioms must be a string list")
    axioms = list(axioms_value)
    standards = {"propext", "Classical.choice", "Quot.sound"}
    native = [item for item in axioms
              if item.endswith("._native.native_decide.ax_1_1")]
    require(len(axioms) == 21 and len(set(axioms)) == 21,
            "final axiom set must contain exactly 21 distinct entries")
    require(standards.issubset(axioms),
            "final axiom set omits a standard kernel dependency")
    unexpected = [item for item in axioms
                  if item not in standards and item not in native]
    require(not unexpected, f"unexpected final axioms: {unexpected}")
    require(len(native) == 18,
            "final axiom set must contain exactly eighteen native axioms")
    for task in tasks:
        suffix = task.theorem + "._native.native_decide.ax_1_1"
        matching = [item for item in native if item.endswith(suffix)]
        require(len(matching) == 1,
                f"expected one native axiom for {task.theorem}")
    return axioms


def audit_module_records(
        snapshot: SnapshotAudit, final_ready: dict[str, Any],
        artifact_root: Path, final_run_remote: PurePosixPath,
        certificates: list[dict[str, Any]]) -> dict[str, Any]:
    records = final_ready.get("moduleRecords")
    require(type(records) is list and len(records) == 79,
            "FINAL_READY must contain exactly 79 module records")
    certificate_by_module = {item["module"]: item for item in certificates}
    certificate_modules = set(certificate_by_module)
    final_audit_log: Path | None = None
    analytic_count = 0
    native_count = 0

    for position, (record, module) in enumerate(zip(records, snapshot.order)):
        field = f"moduleRecords[{position}]"
        require(type(record) is dict, f"{field}: expected object")
        require(record.get("module") == module,
                f"{field}: module order differs from source closure")
        require(record.get("sourceSha256") == snapshot.source_hashes[module],
                f"{field}: source SHA-256 mismatch")
        _, expected_olean = expected_build_paths(snapshot.snapshot_id, module)
        require(record.get("oleanPath") == expected_olean,
                f"{field}: unexpected .olean path")
        olean_local = audit_hashed_artifact(
            expected_olean, record.get("oleanSha256"), artifact_root,
            f"{field}.olean", nonempty=True)

        if module in certificate_modules:
            require_exact_keys(record, NATIVE_RECORD_KEYS, field)
            require(record.get("role") == "source-bound native proof root",
                    f"{field}: native record role mismatch")
            require(sha256_file(olean_local).upper() ==
                    certificate_by_module[module]["oleanSha256"],
                    f"{field}: final record and certificate .olean differ")
            native_count += 1
            continue

        require_exact_keys(record, ANALYTIC_RECORD_KEYS, field)
        require(record.get("role") ==
                "fresh final analytic/assembly elaboration",
                f"{field}: analytic record role mismatch")
        require_exact_int(record.get("exitCode"), 0,
                          f"{field}.exitCode")
        finite_number(record.get("elapsedSeconds"),
                      f"{field}.elapsedSeconds")
        stem = f"{position:03d}-{module}"
        expected_log = str(final_run_remote / f"{stem}.log")
        expected_time = str(final_run_remote / f"{stem}.time.txt")
        require(record.get("logPath") == expected_log and
                record.get("timePath") == expected_time,
                f"{field}: finalization log/time path mismatch")
        require(record.get("command") == expected_lean_command(
            snapshot.snapshot_id, module, expected_time, expected_olean),
            f"{field}: Lean command mismatch")
        log_local = audit_hashed_artifact(
            expected_log, record.get("logSha256"), artifact_root,
            f"{field}.log")
        audit_hashed_artifact(
            expected_time, record.get("timeSha256"), artifact_root,
            f"{field}.time", nonempty=True)
        if module == "Path2Post044TargetAwareConcreteFinalAxiomAudit":
            require(final_audit_log is None,
                    "final axiom audit appears more than once")
            final_audit_log = log_local
        analytic_count += 1

    require(native_count == 18 and analytic_count == 61,
            "final module role counts must be 18 native plus 61 analytic")
    require(final_audit_log is not None,
            "final axiom-audit log is absent from module records")
    logged_axioms = parse_axiom_log(final_audit_log)
    declared_axioms = audit_axioms(final_ready.get("finalAxioms"),
                                   snapshot.tasks)
    require(logged_axioms == declared_axioms,
            "FINAL_READY axioms differ from the hashed final audit log")
    return {
        "moduleCount": len(records),
        "analyticModuleCount": analytic_count,
        "nativeCertificateModuleCount": native_count,
        "finalAxioms": declared_axioms,
        "finalAxiomLogSha256": sha256_file(final_audit_log).upper(),
    }


def audit_final_evidence(snapshot_root: Path, final_ready_path: Path,
                         artifact_root: Path) -> dict[str, Any]:
    artifact_root = artifact_root.resolve()
    require(artifact_root.is_dir(),
            f"artifact mirror root is missing: {artifact_root}")
    final_ready_path = final_ready_path.resolve()
    require(final_ready_path.is_file(),
            f"FINAL_READY is missing: {final_ready_path}")
    try:
        final_relative = final_ready_path.relative_to(artifact_root)
    except ValueError as error:
        raise AuditFailure(
            "FINAL_READY must be inside the artifact mirror root") from error
    require(len(final_relative.parts) == 3 and
            final_relative.parts[0] == "runs" and
            final_relative.parts[2] == "FINAL_READY.json",
            "FINAL_READY mirror path must be runs/finalization-JOB/FINAL_READY.json")
    final_run_name = final_relative.parts[1]
    final_run_match = FINALIZATION_RUN_RE.fullmatch(final_run_name)
    require(final_run_match is not None,
            "FINAL_READY parent is not a canonical finalization run")
    final_run_remote = REMOTE_NOVA_ROOT / "runs" / final_run_name

    snapshot = audit_snapshot(snapshot_root)
    final_ready = read_json_object(final_ready_path, "FINAL_READY")
    require_exact_keys(final_ready, FINAL_READY_KEYS, "FINAL_READY")
    exact_values = {
        "purpose": "source-bound final Path 2 theorem and trust audit",
        "proofEvidence": True,
        "snapshotId": snapshot.snapshot_id,
        "snapshotKind": "final-proof",
        "path2SourceRoot": FINAL_SOURCE_ROOT,
        "sourceManifestSha256": snapshot.snapshot_id.upper(),
        "targetConstant": TARGET_CONSTANT,
        "finalTheorem": FINAL_THEOREM,
        "moduleCount": 79,
        "slurmJobId": final_run_match.group(1),
    }
    for key, expected in exact_values.items():
        actual = final_ready.get(key)
        if type(expected) in (bool, int):
            require(type(actual) is type(expected) and actual == expected,
                    f"FINAL_READY.{key}: expected {expected!r}")
        else:
            require(actual == expected,
                    f"FINAL_READY.{key}: expected {expected!r}")
    require(type(final_ready.get("hostname")) is str and
            COMPUTE_HOST_RE.fullmatch(final_ready["hostname"]) is not None,
            "FINAL_READY hostname is not a Nova compute node")
    finite_number(final_ready.get("finishedAtUnix"),
                  "FINAL_READY.finishedAtUnix", positive=True)
    require_sha256(final_ready.get("baseReadySha256"),
                   "FINAL_READY.baseReadySha256")
    inventory = audit_evidence_manifest(
        final_ready, artifact_root, final_run_remote)

    certificates, base_ready_path = audit_certificate_results(
        snapshot, final_ready, artifact_root)
    base_ready = audit_base_ready(
        snapshot, final_ready, base_ready_path, artifact_root)
    modules = audit_module_records(
        snapshot, final_ready, artifact_root, final_run_remote,
        certificates)

    return {
        "schema": "path2-final-evidence-acceptance-v1",
        "status": "PASS",
        "proofEvidence": True,
        "targetConstant": TARGET_CONSTANT,
        "finalTheorem": FINAL_THEOREM,
        "snapshotId": snapshot.snapshot_id,
        "snapshotFileCount": len(snapshot.manifest_records),
        "interfaceAudit": snapshot.interface_audit,
        "finalReadyRelativePath": final_relative.as_posix(),
        "finalReadySha256": sha256_file(final_ready_path).upper(),
        "evidenceInventory": inventory,
        "baseReady": base_ready,
        "certificateResults": certificates,
        "moduleAudit": modules,
        "trustBoundary": {
            "kernelCheckedFreshAnalyticModules": 61,
            "nativeDecideCertificateModules": 18,
            "nativeDecideIsKernelAxiom": True,
            "externalSearchIsProofEvidence": False,
        },
        "verifierSha256": sha256_file(Path(__file__).resolve()).upper(),
    }


def write_receipt(path: Path, payload: dict[str, Any]) -> str:
    path = path.resolve()
    require(not path.exists(), f"refusing to overwrite receipt: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    serialized = (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode(
        "utf-8")
    descriptor, temporary_name = tempfile.mkstemp(
        prefix="." + path.name + ".", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(serialized)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary_name, path)
    except Exception:
        try:
            os.close(descriptor)
        except OSError:
            pass
        try:
            Path(temporary_name).unlink(missing_ok=True)
        except OSError:
            pass
        raise
    return hashlib.sha256(serialized).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root-preflight", type=Path,
                        help="scan one durable 79-module Path 2 source root")
    parser.add_argument("--snapshot-root", type=Path,
                        help="extracted immutable final snapshot root")
    parser.add_argument("--artifact-root", type=Path,
                        help="local mirror of the fixed Nova project root")
    parser.add_argument("--final-ready", type=Path,
                        help="mirrored runs/finalization-JOB/FINAL_READY.json")
    parser.add_argument("--write-receipt", type=Path,
                        help="atomically write, but never overwrite, a receipt")
    arguments = parser.parse_args()
    try:
        if arguments.source_root_preflight is not None:
            require(arguments.snapshot_root is None and
                    arguments.artifact_root is None and
                    arguments.final_ready is None and
                    arguments.write_receipt is None,
                    "source-root preflight cannot be combined with final "
                    "evidence arguments")
            order, external, tasks, source_hashes = audit_path2_source_root(
                arguments.source_root_preflight)
            identity_rows = [
                f"{module}\t{source_hashes[module]}"
                for module in order
            ]
            output = {
                "schema": "path2-source-root-preflight-v1",
                "status": "PASS",
                "proofEvidence": False,
                "sourcePreflight": True,
                "sourceRoot": str(
                    arguments.source_root_preflight.resolve()),
                "path2ModuleCount": len(order),
                "analyticModuleCount": len(order) - len(tasks),
                "nativeCertificateModuleCount": len(tasks),
                "externalImportCount": len(external),
                "sourceClosureSha256": hashlib.sha256(
                    "\n".join(identity_rows).encode("utf-8")
                ).hexdigest().upper(),
            }
        else:
            require(arguments.snapshot_root is not None and
                    arguments.artifact_root is not None and
                    arguments.final_ready is not None,
                    "final evidence mode requires --snapshot-root, "
                    "--artifact-root, and --final-ready")
            output = audit_final_evidence(
                arguments.snapshot_root, arguments.final_ready,
                arguments.artifact_root)
            if arguments.write_receipt is not None:
                receipt_sha = write_receipt(arguments.write_receipt, output)
                output = dict(output)
                output["receiptPath"] = str(arguments.write_receipt.resolve())
                output["receiptSha256"] = receipt_sha
        print(json.dumps(output, indent=2, sort_keys=True))
        return 0
    except (AuditFailure, OSError, UnicodeError, json.JSONDecodeError,
            ValueError) as error:
        print(json.dumps({
            "status": "FAIL",
            "proofEvidence": False,
            "error": str(error),
        }, indent=2, sort_keys=True), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
