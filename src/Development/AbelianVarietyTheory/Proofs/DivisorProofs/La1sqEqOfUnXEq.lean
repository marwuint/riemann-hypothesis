import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMetricOfIsOrtho
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FjNormMulExpLeSupFlow
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfLePolyExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalDecayHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealFlowPeriodsSpanEqTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantOrthogonality
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos

noncomputable section

namespace GlobalTheory.CuspUnif

section Decay

open NumberField ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mem_SS_of_decay (X : Data E r) (hr : 0 < r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    {C c : ℝ} (hc : 0 < c) (h : ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ C * Real.exp (-c / X.firstMinimumSq x)) : P ∈ X.SS la := by
  have := GlobalTheory.ModeDecay.nonempty_cmType X
  set f : ℝ := (Fintype.card X.Ψ : ℝ) with hf
  have hf0 : 0 < f := Nat.cast_pos.2 Fintype.card_pos
  have hπ := Real.pi_pos
  refine ⟨hP, fun ξ hξ x hx => GlobalTheory.ModeDecay.fj_eq_zero_of_decay GlobalTheory.fj_norm_mul_exp_le_sup_flow
    ReciprocityTheory.ChartRestriction.G.AR.Inst.la1GGStatement_firstMinimum r X la P (c / (8 * Real.pi * f)) hP.1
    ⟨Real.sqrt |C|, 0, le_rfl, fun y hy η hη h2 => ?_⟩ ξ hξ 0 (by simpa using by positivity) x hx⟩
  set t := ⨅ τ, X.tt η y τ with ht
  have ht2 : 2 ≤ t := le_ciInf h2
  have ht' : 0 < t := by linarith
  have hpos : ∀ v : Fin r → E, v ≠ 0 → ∀ τ, 0 < X.c τ * X.maj y τ (Data.emb τ.1 v) := fun v hv τ =>
    mul_pos (TwoSidedBoostBounds.c_pos X τ) (X.maj_pos hy τ (emb_ne_zero τ.1 hv))
  have hle : ∀ τ, X.c τ * X.maj y τ (Data.emb τ.1 η) ≤ 1 / t := fun τ =>
    (le_one_div ht' (hpos η hη.2.2 τ)).1 (ciInf_le (f := fun τ => X.tt η y τ) (Finite.bddBelow_range _) τ)
  have hla : X.firstMinimumSq y ≤ f / t :=
    calc X.firstMinimumSq y ≤ ∑ τ, X.c τ * X.maj y τ (Data.emb τ.1 η) := by
          refine csInf_le ⟨0, ?_⟩ ⟨η, hη.1, hη.2.2, rfl⟩
          rintro _ ⟨v, -, hv, rfl⟩
          exact Finset.sum_nonneg fun τ _ => (hpos v hv τ).le
      _ ≤ ∑ _τ : X.Ψ, 1 / t := Finset.sum_le_sum fun τ _ => hle τ
      _ = f / t := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
  have hla0 : 0 < X.firstMinimumSq y := Real.sqrt_pos.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom X hr hy)
  have hexp : Real.exp (-c / X.firstMinimumSq y) ≤ Real.exp (-4 * Real.pi * (c / (8 * Real.pi * f)) * t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have : c / (f / t) ≤ c / X.firstMinimumSq y := div_le_div_of_nonneg_left hc.le hla0 hla
    have e1 : ((2 : ℕ) : ℝ) * (-4 * Real.pi * (c / (8 * Real.pi * f)) * t) = -(c / (f / t)) := by
      push_cast
      field_simp
      norm_num
    rw [e1, neg_div]
    linarith
  rw [Real.rpow_zero, mul_one]
  refine (Real.le_sqrt_of_sq_le ((h y hy).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left hexp (abs_nonneg C))))).trans_eq ?_
  rw [Real.sqrt_mul (abs_nonneg C), Real.sqrt_sq (Real.exp_pos _).le]

end Decay

end GlobalTheory.CuspUnif
