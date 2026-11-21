import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSum
open DividedPowers CrystallineSemistableComparison.Pb

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatCplB

section Concrete
open Lat
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem smul_def' (u : W) (x : A f ξ l M) : u • x = ofW f ξ l M u * x := rfl

end Concrete

end GlobalTheory.CompanionTheory.LatCplB
