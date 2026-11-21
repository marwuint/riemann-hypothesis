import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited

noncomputable section

open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker

namespace GlobalTheory.WeilM

theorem eventually_comp_eq {P V : Type} [TopologicalSpace P] [TopologicalSpace V] {p₀ : P} (f g : P → V → V)
    (hf : Continuous fun q : P × V => f q.1 q.2) (hg : Continuous fun q : P × V => g q.1 q.2)
    (f0 : ∀ v, f p₀ v = v) (g0 : ∀ v, g p₀ v = v) (hgf : ∀ p v, g p (f p v) = v) {φ : V → ℂ} (hφ : φ ∈ SB V) :
    ∀ᶠ p in 𝓝 p₀, ∀ v, φ (f p v) = φ v := by
  have key : ∀ f : P → V → V, (Continuous fun q : P × V => f q.1 q.2) → (∀ v, f p₀ v = v) →
      ∀ᶠ p in 𝓝 p₀, ∀ v ∈ tsupport φ, φ (f p v) = φ v := fun f hf f0 => by
    refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun v _ => ?_
    filter_upwards [(hφ.1.comp_continuous hf).eventually_eq (p₀, v),
      (hφ.1.comp_continuous continuous_snd).eventually_eq (p₀, v)] with q h1 h2
    simp only [Function.comp, f0] at h1 h2
    rw [h1, h2]
  filter_upwards [key f hf f0, key g hg g0] with p h1 h2 v
  by_cases hv : v ∈ tsupport φ
  · exact h1 v hv
  · by_cases hw : f p v ∈ tsupport φ
    · rw [← h2 _ hw, hgf]
    · rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hw]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem eventually_char_eq_one (μ : Fˣ →* Circle) (hμ : Continuous μ) :
    ∀ᶠ t in 𝓝 (1 : Fˣ), μ t = 1 ∧ distribHaarChar F t = 1 := by
  have h0 : {t : Fˣ | ‖(μ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Fˣ) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨U, hU, hUV⟩ := h0
  have h1 : (fun x : F => 1 + x) ⁻¹' U ∈ 𝓝 (0 : F) :=
    (Continuous.tendsto' (by fun_prop) _ _ (by simp) : Tendsto (fun x : F => 1 + x) (𝓝 0) (𝓝 ((1 : Fˣ) : F))) hU
  have h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) := (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩
  obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset (inter_mem h1 h2)
  have h3 : Tendsto (fun t : Fˣ => (t : F) - 1) (𝓝 1) (𝓝 0) := Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [h3.eventually (SplitWeil.cball_mem_nhds s)] with t ht
  have hv : valuation F (t : F) = 1 := by simpa using (valuation F).map_one_add_of_lt (hs ht).2
  have hn : ∀ n : ℕ, (t : F) ^ n - 1 ∈ SplitWeil.cball s := fun n => by
    induction n with
    | zero => simp [SplitWeil.cball]
    | succ n ih =>
      rw [show (t : F) ^ (n + 1) - 1 = t * (t ^ n - 1) + (t - 1) by ring]
      refine SplitWeil.add_mem_cball ?_ ht
      show valuation F ((t : F) * ((t : F) ^ n - 1)) ≤ valuation F (s : F)
      rw [map_mul, hv, one_mul]
      exact ih
  refine ⟨Circle.coe_eq_one.mp (eq_one_of_forall_pow_near fun n => ?_),
    NNReal.coe_injective (SplitWeil.nabs_eq_one_of_valuation_eq_one hv)⟩
  have : t ^ n ∈ Units.val ⁻¹' U := by simpa using (hs (hn n)).1
  simpa using hUV this

variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

variable [Invertible (2 : F)] {JA : Matrix α α (F × F)} {JB : Matrix β β (F × F)}

end GlobalTheory.WeilM

end
