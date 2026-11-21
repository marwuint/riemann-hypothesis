import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiagMemCongruencePairs

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob.Iota

variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in
private theorem one_le_inv_differentIdeal :
    (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ := by
  have h := FractionalIdeal.inv_anti_mono (K := E)
    (I := (↑(differentIdeal ℤ (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) (J := 1)
    (by simp [differentIdeal_ne_bot]) one_ne_zero FractionalIdeal.coeIdeal_le_one
  simpa using h

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in

theorem _root_.GlobalTheory.SgGlob.Iota.one_mem_dInv (j : ℕ) : (1 : E) ∈ _root_.GlobalTheory.SgGlob.dInv E j := by
  unfold _root_.GlobalTheory.SgGlob.dInv
  have hpow : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ ^ j := by
    simpa using pow_le_pow_left' (one_le_inv_differentIdeal (E := E)) j
  exact hpow (FractionalIdeal.one_mem_one _)

theorem mem_frameLat (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ frameLat P ↔ ∃ a : Fin (r + 1) → E, (∀ b : Fin (r + 1), a b ∈ dInv E (r - (b : ℕ))) ∧ P *ᵥ a = v := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, a, ha, rfl⟩ := hx
      refine ⟨Pi.single b a, fun b' => ?_, by ext i; simp [mul_comm]⟩
      by_cases h : b' = b
      · subst h
        simpa using ha
      · rw [Pi.single_eq_of_ne h]
        exact FractionalIdeal.zero_mem _
    | zero => exact ⟨0, fun b => FractionalIdeal.zero_mem _, Matrix.mulVec_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, fun i => Submodule.add_mem (dInv E (r - (i : ℕ))).coeToSubmodule (ha i) (hb i),
        Matrix.mulVec_add _ _ _⟩
    | smul t x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨t • a, fun i => Submodule.smul_mem (dInv E (r - (i : ℕ))).coeToSubmodule t (ha i),
        Matrix.mulVec_smul _ _ _⟩
  · rintro ⟨a, ha, rfl⟩
    have : P *ᵥ a = ∑ b, a b • fun i => P i b := by
      ext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun b _ => Submodule.subset_span ⟨b, a b, ha b, rfl⟩

theorem mem_span_frameLat (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ Submodule.span E (frameLat P : Set (Fin n → E)) ↔ ∃ a, P *ᵥ a = v := by
  constructor
  · intro hv
    refine (Submodule.span_le (p := LinearMap.range P.mulVecLin)).2 (fun w hw => ?_) hv
    obtain ⟨a, -, rfl⟩ := (mem_frameLat P w).1 hw
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    have : P *ᵥ a = ∑ b, a b • fun i => P i b := by
      ext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span
      (Submodule.subset_span ⟨b, 1, one_mem_dInv _, (one_smul _ _).symm⟩))

end GlobalTheory.SgGlob.Iota
