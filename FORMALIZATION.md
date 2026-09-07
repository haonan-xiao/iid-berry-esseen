# Lean formalization of the 0.4395 bound

Start at [BerryEsseen.lean](BerryEsseen.lean). It imports
[Theorems.Bound04395](lean/BerryEsseen/Theorems/Bound04395.lean), which exports
the theorem `BerryEsseen.iidBerryEsseen879_2000`.

## Mathematical interface

For independent identically distributed real random variables X_k, assume
E X_0 = 0, E X_0^2 = 1, and rho = E |X_0|^3 < infinity. For every integer
n >= 1, the Kolmogorov distance between the normalized sum and the standard
normal law is at most (879/2000) rho / sqrt(n). The Lean statement uses a
probability measure P, iIndepFun, IdentDistrib, and MemLp id 3 (P.map (X 0)).
The conclusion IIDBerryEsseen879_2000Conclusion quantifies over every
positive sample size, without an additional symmetry or support assumption.

## Reading the proof

All proof modules are under `lean/BerryEsseen/`, grouped by mathematical
role. The main theorem is `Theorems.Bound04395`. Comparison results and
diagnostic checks are separated under `Verification/`; they are not
alternative versions of the main theorem.

| Paper argument | Module or directory |
| --- | --- |
| Probability definitions and normalization | Probability.Definitions; Probability.SumMoments |
| Shared parameter and first absolute moment, Section 2 | Moments.ThirdMomentRatio; Moments.FirstAbsoluteMoment |
| Two-point and Gaussian comparisons, Section 3 | CharacteristicFunctions.TwoPointComparison, ComponentBounds, GaussianCorrection, ExponentialModulus |
| Finite-sample smoothing, Section 4 | Smoothing.FiniteEnvelope; CharacteristicFunctions.FiniteSumComparison |
| Large samples and variable exponent, Section 4 | Smoothing.LargeSampleComparison, VariableExponentComparison, UniversalSplit |
| Interval bounds and soundness, Section 5 | Interval/Arithmetic/, Interval/Prawitz/, Interval/Finite/, Interval/Large/, Interval/Small/ |
| Concrete certificates and assembly, Section 5 | Certificates/Finite/, Certificates/Small/, Certificates/Large/ |
| Final numerical implication and theorem | Theorems.NumericalAssembly; Theorems.Bound04395 |
| Final axiom audit | Verification.FinalAxiomAudit |

[proof-guide.md](proof-guide.md) gives the detailed formula-to-lemma
correspondence, including the parameter boundaries, tails and normalization.

The main source groups are:

    lean/BerryEsseen/
      Probability/               Laws, normalized sums and general bounds
      Analysis/                  Exponential and trigonometric inequalities
      Moments/                   First absolute moment constraints
      CharacteristicFunctions/   Component, modulus and comparison bounds
      Smoothing/                 Finite- and large-sample bounds
      Interval/
        Arithmetic/              Dyadic arithmetic and integration
        Prawitz/                 Kernel bounds and fixed-exponent cells
        Finite/ Large/ Small/    Evaluators and soundness
      Certificates/
        Data/                    Partition inputs
        Finite/N01/ ... N99/      Per-sample-size assembly and subtrees
        Finite/Batches/           Assembly over sample-size ranges
        Large/ Small/            Large-sample parameter regions
      Theorems/                  The 0.4395 theorem and its assembly
      Verification/
        Comparisons/             Implications between bound statements
        Subdivision/             Diagnostic correctness and fuel monotonicity
        ...                      Axiom audits

There are 2,309 generated numerical subtree modules. These are individual
finite computations, not 2,309 separate mathematical arguments. Read the
evaluator and coverage proofs before opening individual certificate shards.

The 102 text inputs used to recover subdivision trees are in
`lean/certificate-data/`, outside the module tree. They are read by
`Certificates.Data.FinitePartitions` and
`Certificates.Data.LargeSamplePartitions`, not compiled as old proof modules.
The 14 unused 0.45 aggregate modules have been removed from this version;
the published 0.45 proof remains available in Git history.

`Verification.Comparisons.CertificateImplication` retains the conditional
0.44 statement used by the comparison checks.
`Verification.Comparisons.ConclusionMonotonicity` verifies that the 0.4395
conclusion implies the weaker 0.44 and 0.45 conclusions. Neither module
is imported by the main theorem.

## Build and replay

Run commands from the repository root. Lean 4.29.1, Mathlib v4.29.1 and
StatLean are pinned by lean-toolchain and lake-manifest.json. Do not upgrade
dependencies when reproducing the recorded result.

    lake exe cache get
    lake build BerryEsseen

For a concurrency-limited replay with source-bound resumable checkpoints:

    python lean/scripts/replay.py --build-dir .runtime/replay --jobs 8

Choose jobs for the CPU allocation actually available; no GPU is needed.
The runner invokes no remote scheduler. One runner owns each output
directory. Repeating the command reuses validated successful checkpoints;
a new empty directory gives an independent fresh computation.
REPLAY_READY.json is written only after all 2,480 modules and the exact
final axiom inventory pass. Full evaluation is substantial CPU work.

The lightweight source check does not execute Lean:

    python lean/scripts/replay.py --check-sources

It compares the publication sources with the immutable executed-source
archive using evidence/verification/source-layout.json. Only module paths,
identifiers, relative literal-input paths and comments may change.
Proof expressions and certificate strings are preserved. This includes
the 66 shared proof modules; all 102 literal input files remain byte-identical.

## Executed evidence and trust boundary

The full verification of the 0.4395 bound passed all 2,480 module records. Its 73 non-native
modules were freshly re-elaborated against the successful native witnesses.
The final axiom audit contained 2,407 native witnesses plus propext,
Classical.choice and Quot.sound. The records are described in
[evidence/](evidence/), alongside the build environment used for that
verification and the complete execution archive.

The publication layout has passed the exact source-transformation check
and selected fresh analytic builds. A complete numerical replay under
the new names has not yet been performed. The mapped list in
evidence/verification/publication-axioms.txt is the expected inventory for that replay,
not a newly executed axiom audit.

Lean's kernel checks the analytic implications, interval containment,
continuous coverage and theorem assembly. Concrete Boolean facts use
native_decide, which additionally trusts Lean's native compiler.
The accepted theorem closure contains no sorry or user-declared axioms.
Partition search and scheduling verdicts are not theorem premises.

The 0.4395 execution archive has SHA-256
fc8fc61454025e27ae5508ec438ecc56c5f6318d35b0b20f94b14783e7d9f84f.
To audit its execution evidence independently, choose a destination that
does not already exist:

    python lean/scripts/verification/verify_archive.py --extract evidence/subtree-final-evidence.tar.gz --sha256 fc8fc61454025e27ae5508ec438ecc56c5f6318d35b0b20f94b14783e7d9f84f --destination .runtime/accepted-evidence --snapshot-id 9c1e559233d9df46fffb39e0e4171ffaa2a89d1ea954ab816f7fa9844fbee546

This checks the executed sources, imports, objects, literal inputs, logs,
exit codes and fresh assembly. Paths and job identifiers in the archive
are historical evidence, not prerequisites for portable reproduction.
