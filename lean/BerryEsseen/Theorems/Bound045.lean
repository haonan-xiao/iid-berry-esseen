import BerryEsseen.Analytic
import BerryEsseen.Universal
import BerryEsseen.MomentGeometry
import BerryEsseen.SineCircle
import BerryEsseen.ConvexMinorant
import BerryEsseen.BreakpointCertificate
import BerryEsseen.BreakpointNumerics
import BerryEsseen.DyadicInterval
import BerryEsseen.DyadicPower
import BerryEsseen.DyadicElementary
import BerryEsseen.DyadicDarboux
import BerryEsseen.OneStepDisk
import BerryEsseen.Prawitz
import BerryEsseen.PrawitzCotangentBounds
import BerryEsseen.DyadicPrawitzCotangent
import BerryEsseen.PrawitzKernelEnvelopes
import BerryEsseen.DyadicPrawitzKernel
import BerryEsseen.PrawitzHQLower
import BerryEsseen.DyadicPrawitzHQLower
import BerryEsseen.PrawitzDiskCandidates
import BerryEsseen.PrawitzDbound
import BerryEsseen.DyadicPrawitzDbound
import BerryEsseen.PrawitzE1
import BerryEsseen.DyadicPrawitzE1
import BerryEsseen.PrawitzSmoothingInequality
import BerryEsseen.ExplicitSmoothing
import BerryEsseen.Assembly
import BerryEsseen.PrawitzConcreteNumericalCertificate

/-!
# Berry--Esseen constant 0.45

This is the root module for the Route B formalization. It exports the
source-faithful theorem interface, complete analytic reduction, exact
breakpoint/minorant certificate, proved-sound dyadic checker and continuous
coverage assembly, and the concrete theorem `iidBerryEsseen45`. Acceptance of
that final export requires a successful build of every imported
`native_decide` leaf certificate and the final axiom audit.
-/
