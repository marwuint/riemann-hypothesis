import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusDoubleSeriesHasSumAndNormBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTiltUntiltLeOfFrobeniusSeriesSizeLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesRadiusSizeLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesNatCombinationApprox
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOverPadicOfIndepModPrime

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem Lam_indep_of_first_terms : ∀ (l : ℕ) [Fact l.Prime] (h d : ℕ) (r : ℝ) (y : Fin d → ℕ → Fl l), 2 ≤ h → 0 ≤ r → r < 1 → (∀ a k, ‖sh (y a k)‖ ≤ r) → (∀ n : Fin d → ℕ, ‖sh (∑ a, n a • y a 0)‖ ≤ r ^ l ^ h → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0 := by
  intro l _ h d r y hh hr0 hr1 hy hdet c hc
  have h1 : 1 ≤ h := by omega
  refine _root_.GlobalTheory.indep_over_Ql_of_indep_mod_l l d (Fin 2) (fun a i => abelian₂ h i (y a)) (fun i => gam l h i r) ?_ ?_ c ?_
  · intro a i
    exact (_root_.GlobalTheory.PSer.Lam_main l h i r (y a) h1 hr1 (hy a)).2.2.1
  · intro n hn
    apply hdet n
    have hls := fun j => _root_.GlobalTheory.PSer.lamsum l h j d r (fun a => y a 0) n h1 hr0 hr1 (fun a => hy a 0)
    have hρ0 : 0 ≤ r ^ l ^ h := pow_nonneg hr0 _
    have hρ1 : r ^ l ^ h < 1 := pow_lt_one₀ hr0 hr1 (pow_pos (Fact.out : l.Prime).pos h).ne'
    refine _root_.GlobalTheory.PSer.norm_sh_le_of_lam_le l h (r ^ l ^ h) (∑ a, n a • y a 0) hh hρ0 hρ1 (lt_of_le_of_lt (hls 0).1 hr1) ?_
    intro j hj
    have hG := _root_.GlobalTheory.gam_laws l h j r h1 hr0 hr1
    rw [hG.2.2.2.2.1]
    have hnn : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r := mul_nonneg (norm_nonneg _) hG.2.2.1
    have hA := (hls j).2
    have hB : ‖∑ a, (n a : ℂ_[l]) * (lam h j (y a 0) - abelian₂ h j (y a))‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hnn fun a _ => ?_
      rw [norm_mul]
      have hb := (_root_.GlobalTheory.PSer.Lam_main l h j r (y a) h1 hr1 (hy a)).2.1
      rw [norm_sub_rev] at hb
      calc ‖(n a : ℂ_[l])‖ * ‖lam h j (y a 0) - abelian₂ h j (y a)‖ ≤ 1 * (‖(l : ℂ_[l])‖ * gam l h j r) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one _ _) hb (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hC : ‖∑ a, (n a : ℂ_[l]) * abelian₂ h j (y a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := hn ⟨j, hj⟩
    have heq : lam h j (∑ a, n a • y a 0) = (lam h j (∑ a, n a • y a 0) - ∑ a, (n a : ℂ_[l]) * lam h j (y a 0)) + (∑ a, (n a : ℂ_[l]) * (lam h j (y a 0) - abelian₂ h j (y a)) + ∑ a, (n a : ℂ_[l]) * abelian₂ h j (y a)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA ?_)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hB hC)
  · intro i
    exact hc i.1 i.2

end GlobalTheory.PSer
