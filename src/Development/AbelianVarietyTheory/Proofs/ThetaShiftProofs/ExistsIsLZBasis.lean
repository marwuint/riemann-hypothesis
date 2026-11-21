import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CountableOfIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsHermOfMemLZ

namespace GlobalTheory.MaxCusp

open NumberField Complex MeasureTheory Module ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

section Space

variable (ι : Type) (d : ℕ)

def hermSub : Submodule ℝ (ι → Fin d → Fin d → ℂ) where
  carrier := {b | IsHerm b}
  add_mem' {a b} ha hb τ i k := by simp only [Pi.add_apply, map_add, ha τ i k, hb τ i k]
  zero_mem' τ i k := by simp
  smul_mem' c b hb τ i k := by
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, hb τ i k]

def hermEquiv : hermSub ι d ≃ₗ[ℝ] (ι → Fin d → Fin d → ℝ) where
  toFun b τ i k := (b.1 τ i k).re + (b.1 τ i k).im
  map_add' a b := by funext τ i k; simp; ring
  map_smul' c b := by funext τ i k; simp; ring
  invFun y := ⟨fun τ i k => ⟨(y τ i k + y τ k i) / 2, (y τ i k - y τ k i) / 2⟩, fun τ i k => by
    apply Complex.ext <;> simp <;> ring⟩
  left_inv b := by
    apply Subtype.ext
    funext τ i k
    have := b.2 τ i k
    apply Complex.ext <;> simp [this] <;> ring
  right_inv y := by funext τ i k; simp; ring

variable {ι d}

end Space

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ} (X : Data E r)

def latZ (d g : ℕ) : Submodule ℤ (hermSub X.Ψ d) :=
  AddSubgroup.toIntSubmodule
  { carrier := {b | b.1 ∈ LZ X d g}
    add_mem' := by
      rintro a b ⟨β, hβ, hγ, e1⟩ ⟨β', hβ', hγ', e2⟩
      refine ⟨β + β', fun i k => ?_, fun i k => ?_, ?_⟩
      · show cc (β i k + β' i k) = β k i + β' k i
        rw [RealEmbeddingCharacters.cc_add', hβ, hβ']
      · obtain ⟨γ, hγi, e⟩ := hγ i k
        obtain ⟨γ', hγi', e'⟩ := hγ' i k
        exact ⟨γ + γ', hγi.add hγi', by simp only [Matrix.add_apply, e, e']; ring⟩
      · rw [embH_add, ← e1, ← e2]; rfl
    zero_mem' := ⟨0, fun i k => by simp [cc], fun i k => ⟨0, isIntegral_zero, by simp⟩,
      by funext τ i k; simp [embH]⟩
    neg_mem' := by
      rintro a ⟨β, hβ, hγ, e1⟩
      refine ⟨-β, fun i k => ?_, fun i k => ?_, ?_⟩
      · show cc (-β i k) = -β k i
        rw [RealEmbeddingCharacters.cc_neg', hβ]
      · obtain ⟨γ, hγi, e⟩ := hγ i k
        exact ⟨-γ, hγi.neg, by simp only [Matrix.neg_apply, e]; ring⟩
      · funext τ i k; simp [embH, e1] }

theorem mem_latZ {g : ℕ} {b : hermSub X.Ψ d} : b ∈ latZ X d g ↔ b.1 ∈ LZ X d g := Iff.rfl

def form : (X.Ψ → Fin d → Fin d → ℂ) →ₗ[ℝ] hermSub X.Ψ d →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun χ b => 2 * pairR X χ b.1)
    (fun χ χ' b => by simp [pairR, add_mul, Finset.sum_add_distrib, mul_add])
    (fun c χ b => by
      simp only [pairR, Pi.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum,
        Complex.re_ofReal_mul, smul_eq_mul]; ring)
    (fun χ b b' => by simp [pairR, Finset.sum_add_distrib, mul_add])
    (fun c χ b => by
      simp only [pairR, Submodule.coe_smul, Pi.smul_apply, Complex.real_smul, mul_left_comm _ (c : ℂ),
        ← Finset.mul_sum, Complex.re_ofReal_mul, smul_eq_mul]; ring)

theorem form_apply (χ : X.Ψ → Fin d → Fin d → ℂ) (b : hermSub X.Ψ d) :
    form X χ b = 2 * pairR X χ b.1 := rfl

end

end GlobalTheory.MaxCusp
