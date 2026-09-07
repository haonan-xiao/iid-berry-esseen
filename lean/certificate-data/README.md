# Subdivision-tree inputs

These 102 files supply subdivision trees to the 0.4395 interval checker:
99 finite-sample files (`finite/N01.lean.txt` through `finite/N99.lean.txt`)
and three large-sample files (`large/Small.lean.txt`, `Middle.lean.txt`,
and `Upper.lean.txt`).

The files contain source text from the 0.45 certificate computation. They
are read as strings, not imported or compiled as Lean modules. The 0.4395
proof extracts their tree descriptions and verifies the inequalities for
its own bound on the resulting cells.

The text is kept byte-for-byte to match the recorded checksums. The readers
are [FinitePartitions.lean](../BerryEsseen/Certificates/Data/FinitePartitions.lean)
and [LargeSamplePartitions.lean](../BerryEsseen/Certificates/Data/LargeSamplePartitions.lean).
