# Path 2 computational acceptance

This directory is the durable compact index of the independently accepted
`879/2000` computation, not a replacement for the full proof or portable
evidence archive. The human proof is `../../../path2-proof.md`.
Manuscript/distribution acceptance is recorded separately from this
immutable computational receipt.

- `acceptance.json`: exact immutable source, archive and verifier identities;
  observed build counts, dependency pins and actual scheduling history.
- `source-manifest.tsv`: byte hashes for the complete accepted Path 2 source
  closure and all 102 relative `include_str` inputs, relative to `lean/`.
- `baseline-manifest.tsv`: unchanged baseline Lean sources and Lake/toolchain
  configuration, independently pinned by the original parent manifest.
- `build-order.json`: complete topological order, direct imports, public roots
  and every module's native theorem identity where applicable.
- `final-axioms.txt`: all 2410 exact final axiom names, one per line.
- `promotion.json`: the nine replaced parent batch proof bodies and their
  old/new hashes; 2398 generated modules are newly promoted. The theorem
  types are unchanged and 181 manifest-covered Path 1 files are unchanged.

The separately transferable full archive is `subtree-final-evidence.tar.gz`
(51,843,097 bytes), with SHA-256
`fc8fc61454025e27ae5508ec438ecc56c5f6318d35b0b20f94b14783e7d9f84f`.
It contains 22,729 inventoried artifacts plus its manifest and final receipt.
The archive includes all logs, source/object/import hashes, fresh replay
records, original source plan, literal inputs and the pinned executor repair.

To independently accept that archive without running Lean, use Python 3
from the package's `lean/` directory:

```text
python scripts/nova/verify_path2_subtree_evidence.py --extract /path/to/subtree-final-evidence.tar.gz --sha256 fc8fc61454025e27ae5508ec438ecc56c5f6318d35b0b20f94b14783e7d9f84f --destination /new/empty/path --snapshot-id 9c1e559233d9df46fffb39e0e4171ffaa2a89d1ea954ab816f7fa9844fbee546
```

The destination must not exist; extraction rejects links, unsafe paths,
extra members and any hash/inventory discrepancy. The accepted verifier
has SHA-256 `723653461150542ff7f4220de034712ff57b793ee885b0e2a8fcc4c755a7de96`.
This audits executed evidence; it is not an independent numerical
recomputation. Full replay is a different operation.

`proofEvidence=false` in the computational receipt is intentional. The
receipt proves only the specified computational and identity checks;
human proof, manuscript, PDF and local distribution acceptance are separate.
Remote publication requires the user's fresh approval of a concrete snapshot.
