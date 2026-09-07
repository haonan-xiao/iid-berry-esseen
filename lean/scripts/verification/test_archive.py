"""Small adversarial checks for the portable subtree evidence boundary."""
import copy
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

from verify_archive import (audit_runtime_record, digest, extract_bundle,
    literal_inputs, audit_literal_inputs, execution_repair_paths, PARENT)
from replay_records import stage_literal_inputs


class EvidenceBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.sid = "a" * 64
        self.build = self.root / "builds" / self.sid
        attempt = self.build / "attempts" / "Proof-1"
        attempt.mkdir(parents=True)
        (attempt / "lean.log").write_text("", encoding="utf-8")
        (attempt / "time.txt").write_text("elapsed 1\n", encoding="utf-8")
        remote = "/work/stat-grad/xhn/berry_esseen_path2/builds/" + self.sid
        parent = "/work/stat-grad/xhn/berry_esseen_path2/builds/"+PARENT+"/workspace/projects/berry-esseen/lean/Path2"
        self.record = dict(module="Proof", snapshotId=self.sid, elapsedSeconds=1,
            logPath="attempts/Proof-1/lean.log", timePath="attempts/Proof-1/time.txt",
            logSha256=digest(attempt / "lean.log"), timeSha256=digest(attempt / "time.txt"),
            dependencyLeanPath="/pinned/lib/lean",
            command=["/usr/bin/time", "-v", "-o", remote+"/attempts/Proof-1/time.txt",
                "lake", "env", "env", "LEAN_PATH="+remote+"/Path2:"+remote+"/external:"+parent+":/pinned/lib/lean",
                "lean", "-j1", "--tstack=32768", "-R", remote+"/Path2",
                "-o", remote+"/attempts/Proof-1/Proof.olean", remote+"/Path2/Proof.lean"])

    def check(self, record):
        audit_runtime_record(self.build, self.build/"Path2", record)

    def test_remote_record_on_local_mirror(self):
        self.check(self.record)

    def test_changed_log_rejected(self):
        (self.build/self.record["logPath"]).write_text("modified")
        with self.assertRaisesRegex(ValueError, "runtime artifact mismatch"):
            self.check(self.record)

    def test_command_change_rejected(self):
        record = copy.deepcopy(self.record)
        record["command"][9] = "-j32"
        with self.assertRaisesRegex(ValueError, "unexpected Lean invocation"):
            self.check(record)

    def test_path_escape_rejected(self):
        record = dict(self.record, logPath="../outside")
        with self.assertRaisesRegex(ValueError, "runtime artifact mismatch"):
            self.check(record)

    def test_sorry_even_with_matching_hash_rejected(self):
        path = self.build/self.record["logPath"]
        path.write_text("depends on axioms: [sorryAx]")
        record = dict(self.record, logSha256=digest(path))
        with self.assertRaisesRegex(ValueError, "invalid Lean log"):
            self.check(record)

    def archive(self, names):
        archive = self.root/"evidence.tar.gz"
        with tarfile.open(archive, "w:gz") as handle:
            for name in names:
                info = tarfile.TarInfo(name)
                info.size = 1
                handle.addfile(info, io.BytesIO(b"x"))
        return archive

    def test_archive_traversal_rejected(self):
        archive = self.archive([f"builds/{self.sid}/../../../escape"])
        with self.assertRaisesRegex(ValueError, "unsafe evidence member"):
            extract_bundle(archive, digest(archive), self.root/"extracted", self.sid)
        self.assertFalse((self.root/"escape").exists())

    def test_duplicate_archive_member_rejected(self):
        archive = self.archive([f"builds/{self.sid}/x"] * 2)
        with self.assertRaisesRegex(ValueError, "invalid evidence archive"):
            extract_bundle(archive, digest(archive), self.root/"extracted", self.sid)


class LiteralInputTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.snapshot = self.root / "snapshot"
        self.project = self.root / "parent"
        self.build = self.root / "build"
        (self.snapshot / "sources").mkdir(parents=True)
        (self.project / "BerryEsseen").mkdir(parents=True)
        self.input = self.project / "BerryEsseen" / "Certificate.lean"
        self.input.write_text("certificate input\n", encoding="utf-8")
        self.sha = digest(self.input)
        (self.snapshot / "parent-source-manifest.tsv").write_text(
            f"projects/berry-esseen/lean/BerryEsseen/Certificate.lean\t{self.sha}\t18\n")
        self.source = self.snapshot / "sources" / "Proof.lean"
        self.source.write_text('def input := include_str "../BerryEsseen/Certificate.lean"\n')

    def test_stage_resume_and_audit_exact_input(self):
        self.assertEqual(literal_inputs(self.snapshot), {"BerryEsseen/Certificate.lean": self.sha})
        stage_literal_inputs(self.snapshot, self.project, self.build / "fresh")
        target = self.build / "fresh/BerryEsseen/Certificate.lean"
        modified = target.stat().st_mtime_ns
        stage_literal_inputs(self.snapshot, self.project, self.build / "fresh")
        self.assertEqual(target.stat().st_mtime_ns, modified)
        self.assertEqual(audit_literal_inputs(self.snapshot, self.build),
                         {"BerryEsseen/Certificate.lean": self.sha})

    def test_changed_parent_rejected_before_staging(self):
        self.input.write_text("different")
        with self.assertRaisesRegex(RuntimeError, "parent literal input mismatch"):
            stage_literal_inputs(self.snapshot, self.project, self.build / "fresh")
        self.assertFalse((self.build / "fresh").exists())

    def test_changed_existing_input_not_overwritten(self):
        target = self.build / "fresh/BerryEsseen/Certificate.lean"
        target.parent.mkdir(parents=True)
        target.write_text("different")
        with self.assertRaisesRegex(RuntimeError, "existing literal input mismatch"):
            stage_literal_inputs(self.snapshot, self.project, self.build / "fresh")
        self.assertEqual(target.read_text(), "different")
        with self.assertRaisesRegex(ValueError, "literal input identity mismatch"):
            audit_literal_inputs(self.snapshot, self.build)

    def test_missing_input_rejected(self):
        with self.assertRaisesRegex(ValueError, "literal input identity mismatch"):
            audit_literal_inputs(self.snapshot, self.build)

    def test_unsafe_reference_rejected(self):
        self.source.write_text('def input := include_str "../../elsewhere"\n')
        with self.assertRaisesRegex(ValueError, "unsafe literal input path"):
            literal_inputs(self.snapshot)

    def test_unlisted_reference_rejected(self):
        self.source.write_text('def input := include_str "../BerryEsseen/Other.lean"\n')
        with self.assertRaisesRegex(ValueError, "literal input absent"):
            literal_inputs(self.snapshot)


class ExecutionRepairTests(unittest.TestCase):
    def test_pinned_code_inventory_and_tamper(self):
        with tempfile.TemporaryDirectory() as temp:
            build = Path(temp) / ("a" * 64)
            staging = build / "execution-repair" / "staging"
            staging.mkdir(parents=True)
            names = ["path2_subtree_replay.py", "verify_path2_subtree_evidence.py",
                     "verify_path2_final_evidence.py", "path2_nova.py", "path2_subtree_replay.sbatch"]
            for name in names:
                (staging / name).write_text("test\n")
            manifest = staging / "source-manifest.tsv"
            manifest.write_text("".join(f"{n}\t{digest(staging/n)}\t{(staging/n).stat().st_size}\n"
                                        for n in sorted(names)))
            repair_id = digest(manifest)
            directory = staging.with_name(repair_id)
            staging.rename(directory)
            (build / "EXECUTION_REPAIR.json").write_text(json.dumps(dict(
                repairId=repair_id, snapshotId=build.name, proofEvidence=False)))
            self.assertEqual(len(execution_repair_paths(build)), 7)
            (directory / names[0]).write_text("tampered")
            with self.assertRaisesRegex(ValueError, "execution repair file mismatch"):
                execution_repair_paths(build)


if __name__ == "__main__":
    unittest.main()
