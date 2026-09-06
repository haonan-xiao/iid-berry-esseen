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

All modules below are under lean/BerryEsseen/. The shared analytic and dyadic
modules remain directly in that directory; the additional arguments are
grouped by mathematical role.

| Paper argument | Module or directory |
| --- | --- |
| Shared parameter and first absolute moment, Section 2 | MomentGeometry; Moments.FirstAbsoluteMoment |
| Two-point and Gaussian comparisons, Section 3 | CharacteristicFunctions.TwoPointComparison, ComponentBounds, GaussianCorrection, ExponentialModulus |
| Finite-sample smoothing, Section 4 | Smoothing.FiniteEnvelope; CharacteristicFunctions.FiniteSumComparison |
| Large samples and variable exponent, Section 4 | Smoothing.LargeSampleComparison, VariableExponentComparison, UniversalSplit |
| Interval bounds and soundness, Section 5 | Interval/Finite/, Interval/Large/, Interval/Small/ |
| Concrete certificates and assembly, Section 5 | Certificates/Finite/, Certificates/Small/, Certificates/Large/ |
| Final numerical implication and theorem | Theorems.NumericalAssembly; Theorems.Bound04395 |
| Final axiom audit | Verification.FinalAxiomAudit |

[proof-guide.md](proof-guide.md) gives the detailed formula-to-lemma
correspondence, including the parameter boundaries, tails and normalization.

The main source groups are:

    lean/BerryEsseen/
      Analysis/                  Exponential and trigonometric inequalities
      Moments/                   First absolute moment constraints
      CharacteristicFunctions/   Component, modulus and comparison bounds
      Smoothing/                 Finite- and large-sample bounds
      Interval/
        Finite/ Large/ Small/    Evaluators and soundness
      Certificates/
        Data/                    Partition inputs
        Finite/N01/ ... N99/      Per-sample-size assembly and subtrees
        Finite/Batches/           Assembly over sample-size ranges
        Large/ Small/            Large-sample parameter regions
      Theorems/                  Final probability statements
      Verification/              Axiom and interface audits

There are 2,309 generated numerical subtree modules. These are individual
finite computations, not 2,309 separate mathematical arguments. Read the
evaluator and coverage proofs before opening individual certificate shards.
The historical 0.45 aggregate is Theorems.Bound045, not the default target.

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
archive using lean/evidence/source-layout.json. Only module paths,
identifiers, relative literal-input paths and comments may change.
Proof expressions and certificate strings are preserved, and all 102
literal input files remain byte-identical.

## Executed evidence and trust boundary

The original full run passed all 2,480 module records. Its 73 non-native
modules were freshly re-elaborated against the successful native witnesses.
The final axiom audit contained 2,407 native witnesses plus propext,
Classical.choice and Quot.sound. Original records and names remain in
lean/evidence/path2-4395/ and evidence/subtree-final-evidence.tar.gz.
Their historical identifiers preserve traceability; they are not the
current source layout.

The publication layout has passed the exact source-transformation check
and selected fresh analytic builds. A complete numerical replay under
the new names has not yet been performed. The mapped list in
lean/evidence/final-axioms.txt is the expected inventory for that replay,
not a newly executed axiom audit.

Lean's kernel checks the analytic implications, interval containment,
continuous coverage and theorem assembly. Concrete Boolean facts use
native_decide, which additionally trusts Lean's native compiler.
The accepted theorem closure contains no sorry or user-declared axioms.
Partition search and scheduling verdicts are not theorem premises.

The original archive has SHA-256
fc8fc61454025e27ae5508ec438ecc56c5f6318d35b0b20f94b14783e7d9f84f.
To audit its execution evidence independently, choose a destination that
does not already exist:

    python evidence/tools/verify_path2_subtree_evidence.py --extract evidence/subtree-final-evidence.tar.gz --sha256 fc8fc61454025e27ae5508ec438ecc56c5f6318d35b0b20f94b14783e7d9f84f --destination .runtime/accepted-evidence --snapshot-id 9c1e559233d9df46fffb39e0e4171ffaa2a89d1ea954ab816f7fa9844fbee546

This checks original sources, imports, objects, literal inputs, logs,
exit codes and fresh assembly. Paths and job identifiers in the archive
are historical evidence, not prerequisites for portable reproduction.
