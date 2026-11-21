import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.NablaExpConj

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem Dof_expS (F : Fin d → PS k 2 d) (u : Fin d → k) {g : PS k 1 d}
    (hg : constantCoeff g = 0) : Dof F u (FB.expS k g) = FB.expS k g * Dof F u g := by
  have e : ∀ i, pderiv k i (FB.expS k g) = FB.expS k g * pderiv k i g :=
    FormalCalc.pderiv_formalExp hg
  unfold Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e]
  ring

end GlobalTheory.NablaExpConj
