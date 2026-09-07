# Verification evidence for the 0.4395 bound

This directory contains the records of the completed Lean verification of
the **0.4395** bound and the configuration used for that verification.
To read the proof or build the current sources, start with
[FORMALIZATION.md](../FORMALIZATION.md).

| Contents | Purpose |
| --- | --- |
| [build-environment/](build-environment/) | Lean version, dependency versions and package configuration used for the completed 0.4395 verification |
| [verification/](verification/) | Verification results, source checksums, module dependencies and the final axiom inventory |
| [subtree-final-evidence.tar.gz](subtree-final-evidence.tar.gz) | Complete execution records, including source files, compiled objects and logs |

The proof sources were subsequently reorganized for publication.
The files in `verification/` also record the correspondence between the
verified sources and the published names. The execution archive is unchanged.

The archive checksum and the command for checking its contents are given in
[FORMALIZATION.md](../FORMALIZATION.md#executed-evidence-and-trust-boundary).
