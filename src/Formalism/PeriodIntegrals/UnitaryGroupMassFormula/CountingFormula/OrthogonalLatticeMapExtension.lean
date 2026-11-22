import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrthogonalLatticeSameGenus

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

namespace OrbitSumPf

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

def split (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (hz0 : h1 z z ≠ 0) : VecSplit h1 (hPerp h1 z) where
  x₀ := z
  ι := (wPerp h1 z).subtype
  inj := Subtype.val_injective
  hx₀ := hz0
  isom := fun _ _ => rfl
  orth := fun a => a.2
  cover := fun v => ⟨h1 z v / h1 z z, ⟨v - (h1 z v / h1 z z) • z, by
      show h1 z (v - (h1 z v / h1 z z) • z) = 0
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hz0, sub_self]⟩, by simp⟩

variable {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1}

theorem mul_mem_hz {σ τ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) (hτ : τ ∈ hz h1 z) : σ * τ ∈ hz h1 z := by
  simp only [hz, Set.mem_setOf_eq] at *
  refine ⟨mul_mem hσ.1 hτ.1, ?_⟩
  show σ (τ z) = z
  rw [hτ.2, hσ.2]

theorem inv_mem_hz {σ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) : σ⁻¹ ∈ hz h1 z := by
  simp only [hz, Set.mem_setOf_eq] at *
  refine ⟨inv_mem hσ.1, ?_⟩
  show σ.symm z = z
  rw [LinearEquiv.symm_apply_eq, hσ.2]

variable (hz0 : h1 z z ≠ 0)

private theorem gmap_mul_lemma {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (a b : W ≃ₗ[K] W) (N : Submodule (𝓞 K) W) :
    Formalism.HermitianLatticesTheory.gmap (a * b) N = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b N) := by
  simp only [Formalism.HermitianLatticesTheory.gmap, ← Submodule.map_comp]
  rfl

theorem gmap_inv_gmap' {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (a : W ≃ₗ[K] W) (N : Submodule (𝓞 K) W) : Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a N) = N := by
  rw [← gmap_mul_lemma, inv_mul_cancel]
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem card_stabZ_conj {τ : V1 ≃ₗ[K] V1} (hτ : τ ∈ hz h1 z) (M : Submodule (𝓞 K) V1) :
    Nat.card (stabZ h1 z (Formalism.HermitianLatticesTheory.gmap τ M)) = Nat.card (stabZ h1 z M) := by
  apply Nat.card_congr
  refine
    { toFun := fun σ => ⟨τ⁻¹ * σ.1 * τ, ?_⟩
      invFun := fun σ => ⟨τ * σ.1 * τ⁻¹, ?_⟩
      left_inv := fun σ => Subtype.ext (by simp [mul_assoc])
      right_inv := fun σ => Subtype.ext (by simp [mul_assoc]) }
  · obtain ⟨a1, a2⟩ := σ.2
    exact ⟨mul_mem_hz (mul_mem_hz (inv_mem_hz hτ) a1) hτ, by
      rw [gmap_mul_lemma, gmap_mul_lemma, a2, gmap_inv_gmap']⟩
  · obtain ⟨a1, a2⟩ := σ.2
    refine ⟨mul_mem_hz (mul_mem_hz hτ a1) (inv_mem_hz hτ), ?_⟩
    rw [gmap_mul_lemma, gmap_mul_lemma, gmap_inv_gmap', a2]

end OrbitSumPf

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
