import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefAInnerEqZero

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section admitted

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}

theorem coefB_khw_le (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (C : ℝ) :
    ∃ k : ℕ, ∀ w ∈ genSub E V, ∀ μ : Fin n → ℝ, IsKHWVec ε E μ w → casValK ε μ ≤ C →
      w ∈ layer ε E V k := by
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  refine ⟨⌈(C - casValK ε (lowK ε lam)) / (2 * (h - n + 1))⌉₊, fun w hw μ hμ hμC => ?_⟩
  obtain ⟨w₀, hw₀, -, m, ws, hsum, hws⟩ := k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ
  rw [hsum]
  refine Submodule.add_mem _ (layer_mono (Nat.zero_le _) (show w₀ ∈ layer ε E V 0 from hw₀))
    (Submodule.sum_mem _ fun j _ => ?_)
  by_cases h0 : ws j = 0
  · rw [h0]
    exact Submodule.zero_mem _
  obtain ⟨-, hpos, hle⟩ := (hws j).2 h0
  refine layer_mono ?_ (hws j).1
  have hj : ((j : ℕ) : ℝ) + 1 ≤ (C - casValK ε (lowK ε lam)) / (2 * (h - n + 1)) := by
    rw [le_div_iff₀ (mul_pos two_pos hpos)]
    linarith
  have := hj.trans (Nat.le_ceil _)
  exact_mod_cast this

theorem coefB_adm (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (C : ℝ) :
    ∃ k : ℕ, ∀ y ∈ genSub E V, ∀ θ : ℝ, θ ≤ C → casimirK ε E y = (θ : ℂ) • y →
      y ∈ layer ε E V k := by
  obtain ⟨K, hK⟩ := coefB_khw_le hE hU hV hc hgap C
  refine ⟨K, fun y hy θ hθ hyθ => ?_⟩
  have hUk := isKUnitary_of_isInfUnitary hU
  obtain ⟨m, hm⟩ := exists_layer_of_mem_genSub hE hV.2.1 hy
  have hfm : FiniteDimensional ℂ (layer ε E V m) := finiteDimensional_layer hV.1 m
  set T : Submodule ℂ M := layer ε E V m ⊓ LinearMap.ker (casimirK ε E - (θ : ℂ) • 1) with hTdef
  have memT : ∀ x, x ∈ T ↔ x ∈ layer ε E V m ∧ casimirK ε E x = (θ : ℂ) • x := by
    intro x
    simp only [T, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have hTd : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le inf_le_left
  have hTs : IsKStableSub ε E T := by
    intro a b hab x hx
    rw [memT] at hx ⊢
    refine ⟨layer_kStable hE hV.2.1 m a b hab x hx.1, ?_⟩
    have := congrArg (fun F : Module.End ℂ M => F x) (casimirK_comm ε hE a b hab)
    simp only [Module.End.mul_apply] at this
    rw [this, hx.2, map_smul]
  set T₀ : Submodule ℂ M := T ⊓ layer ε E V K
  have hT0d : FiniteDimensional ℂ T₀ := Submodule.finiteDimensional_of_le inf_le_left
  have hT0s : IsKStableSub ε E T₀ := fun a b hab x hx =>
    ⟨hTs a b hab x hx.1, layer_kStable hE hV.2.1 K a b hab x hx.2⟩
  have hyT : y ∈ T := (memT y).2 ⟨hm, hyθ⟩
  set r := y - T₀.starProjection y
  by_cases hr : r = 0
  · have : y = T₀.starProjection y := sub_eq_zero.1 hr
    rw [this]
    exact (Submodule.starProjection_apply_mem T₀ y).2
  exfalso
  set S : Submodule ℂ M := T ⊓ T₀ᗮ
  have hrS : r ∈ S := ⟨T.sub_mem hyT (Submodule.starProjection_apply_mem T₀ y).1,
    Submodule.sub_starProjection_mem_orthogonal y⟩
  have hSd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le inf_le_left
  have hSs : IsKStableSub ε E S := fun a b hab x hx =>
    ⟨hTs a b hab x hx.1, orthogonal_kStable hUk hT0s a b hab x hx.2⟩
  have hne : S ≠ ⊥ := by
    intro h
    have := hrS
    rw [h, Submodule.mem_bot] at this
    exact hr this
  obtain ⟨w, hwS, hw0, μ, hμ⟩ := exists_khw hE hUk hSd hSs hne
  have hwT := (memT w).1 hwS.1
  have h1 := casimirK_khwVec ε hE hμ
  rw [hwT.2] at h1
  have h2 : (θ : ℂ) = ((nsq (μ + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) := smul_left_injective ℂ hw0 h1
  have h3 : casValK ε μ = θ := by
    have := Complex.ofReal_injective h2
    rw [this]; rfl
  have hwK := hK w (layer_le_genSub m hwT.1) μ hμ (h3 ▸ hθ)
  have hwT0 : w ∈ T₀ := ⟨hwS.1, hwK⟩
  have := Submodule.inner_right_of_mem_orthogonal hwT0 hwS.2
  exact hw0 (inner_self_eq_zero.1 this)

end admitted

section Tr

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]

def coefTr (A : Module.End ℂ (Fin n → D)) : Module.End ℂ (WithLp 2 (Fin n → D)) :=
  (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm.toLinearMap ∘ₗ A ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin n → D)).toLinearMap

theorem coefTr_apply (A : Module.End ℂ (Fin n → D)) (u : WithLp 2 (Fin n → D)) :
    coefTr A u = WithLp.toLp 2 (A (WithLp.ofLp u)) := rfl

end Tr

section Exist

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem coefB_locFin (hE : IsGlRep E) {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) : CoefLocFin (casimirK ε E) (genSub E V) := by
  intro y hy
  obtain ⟨m, hm⟩ := exists_layer_of_mem_genSub hE hVk hy
  exact ⟨layer ε E V m, finiteDimensional_layer hVf m, layer_le_genSub m,
    fun x hx => casimirK_mem_of_kStable (layer_kStable hE hVk m) hx, hm⟩

end Exist

end ReciprocityTheory.ChartRestriction.DS
