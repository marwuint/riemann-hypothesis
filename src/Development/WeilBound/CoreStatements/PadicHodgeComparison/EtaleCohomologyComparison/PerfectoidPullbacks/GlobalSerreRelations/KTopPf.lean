import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreStH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.KIsoPf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationVanishesAboveDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem k_top_pf : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] (d : ℕ)
    [SmoothOfRelativeDimension d q] (j : ℕ), ∀ x ∈ FilR q j (d + 1), x = 0 :=
  _root_.GlobalTheory.CompanionTheory.FilTop.fil_top_vanish locGr_h locVan_h polyTf_h globSerreSt_h globVanSt_h k_iso_pf gr_aff_pf

end CrystallineSemistableComparison.Pb
