import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.LowSpanCombinations
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicThreshold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul

namespace GlobalTheory.FlatCompare

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem levi_eq (X : Data E r) (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : levi X x0 φ z ξ = leviM X φ x0 z ξ := rfl

theorem hf_pos (X : Data E r) {ξ : Fin r → E} (hξ : ξ ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    0 < hf X ξ x τ := by
  unfold hf
  refine mul_pos (IsotropicThreshold.c_pos X τ) (X.maj_pos hx τ ?_)
  intro h0
  apply hξ
  funext a
  have h1 := congrFun h0 a
  simpa [Data.emb] using h1

theorem guard_iff (X : Data E r) {ξ : Fin r → E} (hξ : ξ ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    hf X ξ x τ ≤ 1 ↔ 1 ≤ X.tt ξ x τ := by
  rw [tt_eq X ξ x τ, one_le_div (hf_pos X hξ hx τ)]

theorem logTerm_nonneg (X : Data E r) (x : Frame X.Ψ r) : 0 ≤ Real.log (1 + 1 / X.la1 x) := by
  apply Real.log_nonneg
  have h1 : 0 ≤ 1 / X.la1 x := div_nonneg zero_le_one (Real.sqrt_nonneg _)
  linarith

theorem exists_short (X : Data E r) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, 0 < X.firstMinimumSq x → X.firstMinimumSq x < ε →
    ∃ v, X.IsIso v ∧ (∀ τ, 1 ≤ X.tt v x τ) ∧ ∀ τ, 1 / (2 * X.firstMinimumSq x) ≤ X.tt v x τ := by
  obtain ⟨δ0, hδ0, hiso⟩ := IsotropicThreshold.iso_threshold X
  refine ⟨min (δ0 / 2) (1 / 2), lt_min (by linarith) (by norm_num), fun x hx hpos hsmall => ?_⟩
  have hmin1 := min_le_left (δ0 / 2) (1 / 2)
  have hmin2 := min_le_right (δ0 / 2) (1 / 2)
  have hne : {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : X.firstMinimumSq x = 0 := by rw [Data.firstMinimumSq, hemp, Real.sInf_empty]
    linarith
  obtain ⟨t, ⟨v, hvΛ, hv0, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt hne (show X.firstMinimumSq x < 2 * X.firstMinimumSq x by linarith)
  have hsum_lt : ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) < δ0 := by linarith
  have hherm := hiso x hx v hvΛ hsum_lt
  have hterm : ∀ τ, hf X v x τ ≤ ∑ τ', X.c τ' * X.maj x τ' (Data.emb τ'.1 v) := fun τ =>
    Finset.single_le_sum (f := fun τ' => X.c τ' * X.maj x τ' (Data.emb τ'.1 v))
      (fun τ' _ => (hf_pos X hv0 hx τ').le) (Finset.mem_univ τ)
  refine ⟨v, ⟨hvΛ, hherm, hv0⟩, fun τ => ?_, fun τ => ?_⟩
  · rw [← guard_iff X hv0 hx τ]
    linarith [hterm τ]
  · rw [tt_eq X v x τ]
    exact one_div_le_one_div_of_le (hf_pos X hv0 hx τ) (by linarith [hterm τ])

theorem bdd_add_log (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : cfwM X ps a) (ha : 0 < a)
    (K : ℝ) : ∃ B : ℝ, ∀ x ∈ X.dom, ps x + K * Real.log (1 + 1 / X.la1 x) ≤ B := by
  obtain ⟨⟨C1, A1, h1⟩, h2⟩ := h
  obtain ⟨C2, A2, h2'⟩ := h2 (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨ε, hε, hshort⟩ := exists_short X
  have hM : 0 ≤ |A1| + |K| + |A2| := by positivity
  have hpa : 0 < 8 * Real.pi * a := by positivity
  refine ⟨max (C1 + (|A1| + |K| + |A2|) / Real.sqrt ε)
    (C2 + (|A1| + |K| + |A2|) ^ 2 / (8 * Real.pi * a)), fun x hx => ?_⟩
  have hL0 := logTerm_nonneg X x
  have hy0 : 0 ≤ 1 / X.la1 x := div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hLy : Real.log (1 + 1 / X.la1 x) ≤ 1 / X.la1 x := by
    have h3 := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / X.la1 x by linarith)
    linarith
  have hK := mul_le_mul_of_nonneg_right (le_abs_self K) hL0
  have hA1 := mul_le_mul_of_nonneg_right (le_abs_self A1) hL0
  have hA2 := mul_le_mul_of_nonneg_right (le_abs_self A2) hL0
  have hA1' := mul_nonneg (abs_nonneg A1) hL0
  have hA2' := mul_nonneg (abs_nonneg A2) hL0
  by_cases hs : 0 < X.firstMinimumSq x ∧ X.firstMinimumSq x < ε
  · obtain ⟨v, hv, hv1, hv2⟩ := hshort x hx hs.1 hs.2
    have hb := h2' x hx v hv hv1
    have := nonempty_cmType X
    have hinf : 1 / (2 * X.firstMinimumSq x) ≤ ⨅ τ, X.tt v x τ := le_ciInf hv2
    have hla : X.la1 x ^ 2 = X.firstMinimumSq x := Real.sq_sqrt hs.1.le
    have hyy : 1 / (2 * X.firstMinimumSq x) = (1 / X.la1 x) ^ 2 / 2 := by
      rw [div_pow, one_pow, hla]; ring
    rw [hyy] at hinf
    have hcoef : (0 : ℝ) ≤ 8 * Real.pi * (1 - 2 * (1 / 4)) * a := by nlinarith [Real.pi_pos]
    have hI := mul_le_mul_of_nonneg_left hinf hcoef
    have hMy := mul_le_mul_of_nonneg_left hLy hM
    have hq : (|A1| + |K| + |A2|) * (1 / X.la1 x) - 2 * Real.pi * a * (1 / X.la1 x) ^ 2 ≤
        (|A1| + |K| + |A2|) ^ 2 / (8 * Real.pi * a) := by
      rw [le_div_iff₀ hpa]
      nlinarith [sq_nonneg (4 * Real.pi * a * (1 / X.la1 x) - (|A1| + |K| + |A2|))]
    refine le_trans ?_ (le_max_right _ _)
    linarith
  · have hLe : Real.log (1 + 1 / X.la1 x) ≤ 1 / Real.sqrt ε := by
      rcases le_or_gt (X.firstMinimumSq x) 0 with h0 | h0
      · have hz : X.la1 x = 0 := Real.sqrt_eq_zero'.2 h0
        rw [hz, div_zero, add_zero, Real.log_one]
        positivity
      · have hge : ε ≤ X.firstMinimumSq x := by
          by_contra hlt
          exact hs ⟨h0, not_le.1 hlt⟩
        exact hLy.trans (one_div_le_one_div_of_le (Real.sqrt_pos.2 hε) (Real.sqrt_le_sqrt hge))
    have hb := h1 x hx
    have hMe := mul_le_mul_of_nonneg_left hLe hM
    have he : (|A1| + |K| + |A2|) * (1 / Real.sqrt ε) = (|A1| + |K| + |A2|) / Real.sqrt ε := by ring
    refine le_trans ?_ (le_max_left _ _)
    linarith

theorem cfwM_of_extraBounds (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : ExtraBounds X ps a) :
    cfwM X ps a := by
  obtain ⟨A, h1, C, h2⟩ := h
  refine ⟨⟨C, A, h2⟩, fun η hη _ => ?_⟩
  obtain ⟨C', hC'⟩ := h1 η hη
  exact ⟨C', A, fun x hx ξ hξ htt => hC' x hx ξ hξ fun τ => (guard_iff X hξ.2.2 hx τ).2 (htt τ)⟩

theorem extraBounds_of_cfwM (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : cfwM X ps a) : ExtraBounds X ps a := by
  rcases ha.eq_or_lt with ha0 | hapos
  · subst ha0
    obtain ⟨⟨C, A, hC⟩, -⟩ := h
    refine ⟨A, fun η _ => ⟨C, fun x hx ξ _ _ => ?_⟩, C, hC⟩
    have h1 := hC x hx
    simp only [mul_zero, zero_mul, sub_zero]
    exact h1
  · obtain ⟨B0, hB0⟩ := bdd_add_log X h hapos 0
    have := nonempty_cmType X
    refine ⟨0, fun η hη => ?_, B0, fun x hx => by linarith [hB0 x hx]⟩
    rcases lt_or_ge η (1 / 2) with hη2 | hη2
    · obtain ⟨C', A', hC'⟩ := h.2 (η / 2) (by linarith) (by linarith)
      obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 - 2 * η) / (1 - η) := ⟨_, rfl⟩
      have h1η : 0 < 1 - η := by linarith
      have hθ0 : 0 < θ := by rw [hθ]; exact div_pos (by linarith) h1η
      have hθ1 : θ < 1 := by rw [hθ, div_lt_one h1η]; linarith
      have hθη : θ * (1 - η) = 1 - 2 * η := by rw [hθ]; field_simp
      obtain ⟨K, hK⟩ : ∃ K : ℝ, (1 - θ) * K = θ * |A'| :=
        ⟨θ * |A'| / (1 - θ), by field_simp [(sub_pos.2 hθ1).ne']⟩
      obtain ⟨BK, hBK⟩ := bdd_add_log X h hapos K
      refine ⟨θ * C' + (1 - θ) * BK, fun x hx ξ hξ hg => ?_⟩
      have htt : ∀ τ, 1 ≤ X.tt ξ x τ := fun τ => (guard_iff X hξ.2.2 hx τ).1 (hg τ)
      have hL0 := logTerm_nonneg X x
      have e1 := mul_le_mul_of_nonneg_left (hC' x hx ξ hξ htt) hθ0.le
      have e2 := mul_le_mul_of_nonneg_left (hBK x hx) (sub_pos.2 hθ1).le
      have hKL : (1 - θ) * K * Real.log (1 + 1 / X.la1 x) =
          θ * |A'| * Real.log (1 + 1 / X.la1 x) := by rw [hK]
      have hA : θ * A' * Real.log (1 + 1 / X.la1 x) ≤ θ * |A'| * Real.log (1 + 1 / X.la1 x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self A') hθ0.le) hL0
      have h3 : θ * (8 * Real.pi * (1 - 2 * (η / 2)) * a * ⨅ τ, X.tt ξ x τ) =
          8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ := by
        rw [← hθη]; ring
      linarith
    · refine ⟨B0, fun x hx ξ hξ hg => ?_⟩
      have htt : ∀ τ, 1 ≤ X.tt ξ x τ := fun τ => (guard_iff X hξ.2.2 hx τ).1 (hg τ)
      have hI : 1 ≤ ⨅ τ, X.tt ξ x τ := le_ciInf htt
      have h2 := hB0 x hx
      have hpI : 0 ≤ 8 * Real.pi * a * ⨅ τ, X.tt ξ x τ :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith

theorem extraBounds_iff (X : Data E r) (ps : Frame X.Ψ r → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ExtraBounds X ps a ↔ cfwM X ps a := ⟨fun h => cfwM_of_extraBounds X h, extraBounds_of_cfwM X ha⟩

end

end GlobalTheory.FlatCompare
