import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAcrisTruncatedWittStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittToAcrisIsDPMorphism
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb

theorem dp_wn : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ), IsDPMorphism (Wc.pd l r.k n) (B.DD true (base l) n) (Mid.wn r n) := @_root_.GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism

end CrystallineSemistableComparison.Pb
