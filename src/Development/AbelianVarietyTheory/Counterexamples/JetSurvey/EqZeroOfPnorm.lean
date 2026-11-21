import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupNormFromNet

noncomputable section

namespace GlobalTheory.NetNormExamples

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem pnorm_nonneg (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    0 ≤ X.pnorm la P x :=
  mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg X la x)

theorem pnorm_le_supN (U : Unf Xo c σ r) (la) {P : FDSec U.X} (hP : P ∈ holSub U.X la) (p : FPt U.X) :
    (U.X p.1).pnorm (la p.1) (P p.1) p.2 ≤ supN U.X la P := by
  unfold supN
  rw [← ENNReal.ofReal_le_iff_le_toReal (supE_ne_top _ _ hP)]
  exact le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (P p.1) p.2)) p

theorem eq_zero_of_pnorm (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h0 : X.pnorm la P x = 0) : P x = 0 := by
  have hne : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i e => by
    have := (hx τ).2 i
    rw [e] at this; simp at this
  unfold Data.pnorm at h0
  refine norm_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right (ne_of_gt ?_))
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hne _ _) (hne _ _))) _

end GlobalTheory.NetNormExamples
