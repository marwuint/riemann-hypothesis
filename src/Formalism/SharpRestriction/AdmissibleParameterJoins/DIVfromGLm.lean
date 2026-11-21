import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLb
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLd
import Formalism.SharpRestriction.AdmissibleParameterJoins.LenAtT
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SevenLogLeLOfPowerBound

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

def DlSize {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps

theorem numsL_wtsL_fam {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) :
    ∃ Cn₀ : ℝ, ∀ Cn ≥ Cn₀, ∀ cL ≥ (3 : ℝ), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧ WtsL (Fm.D x i) (Fm.L x i) Cn :=
  flipTwoThree.nums_wts_of_tuSize Fm hT hDl

theorem factDGam_mono {D : D7} {C C' : ℝ} (h : FactDGam D C) (hC : C ≤ C') : FactDGam D C' := by
  intro u
  refine (h u).trans ?_
  have h1 : (0 : ℝ) ≤ Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by
    have : ((D.R.f : ℝ) * D.R.N D.R.m) = ((D.R.f * D.R.N D.R.m : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact Real.log_natCast_nonneg _
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) h1
  have := mul_le_mul_of_nonneg_right hC h2
  simp only [mul_assoc] at this ⊢
  exact this

theorem slopes_family_of_column_values {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) (h5 : flipTwoThree.ConclusionF5 Fm)
    (h6 : flipTwoThree.ConclusionF6 Fm) (hCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) :
    LocalQuadraticParts.SlopesFamily Fm := by
  obtain ⟨Cn, hN⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x0, hN⟩ := hN Cn le_rfl 3 le_rfl
  obtain ⟨x1, hCV⟩ := hCV
  refine family_orderBound_of_fifth_sixth Fm Cn 3 h5 h6 (by norm_num) ⟨max x0 x1, fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_max_left _ _) hx
  have e1 : x ≥ x1 := le_trans (le_max_right _ _) hx
  exact ⟨by linarith [flipTwoThree.two_le_rdE (Fm.D x i).host], (hN x e0 i).1, (hN x e0 i).2, hCV x e1 i⟩

end Formalism.MainNotions.J

end
