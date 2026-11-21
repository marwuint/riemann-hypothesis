import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField Matrix
open scoped ComplexOrder

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def latticeDual {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Submodule (𝓞 K) (Fin m → K) where
  carrier := {φ | ∀ v ∈ L, φ ⬝ᵥ v ∈ Set.range (algebraMap (𝓞 K) K)}
  add_mem' := by
    intro φ ψ hφ hψ v hv
    obtain ⟨a, ha⟩ := hφ v hv
    obtain ⟨b, hb⟩ := hψ v hv
    exact ⟨a + b, by rw [map_add, ha, hb, add_dotProduct]⟩
  zero_mem' := fun v _ ↦ ⟨0, by rw [map_zero, zero_dotProduct]⟩
  smul_mem' := by
    intro c φ hφ v hv
    obtain ⟨a, ha⟩ := hφ v hv
    exact ⟨c * a, by rw [map_mul, ha, smul_dotProduct, Algebra.smul_def]⟩

structure IsDualBasis {m N : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) (φ : Fin (N + 1) → Fin m → K) : Prop where
  independent : LinearIndependent ℤ φ
  span_eq : Submodule.span ℤ (Set.range φ) = (latticeDual L).restrictScalars ℤ

def latticeForm {m : ℕ} (φ : Fin m → K) : MvPolynomial (Fin m) K := ∑ j, C (φ j) * X j

def latticeMap {m N : ℕ} (φ : Fin (N + 1) → Fin m → K) :
    MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ →+* MvPolynomial (Fin m) K :=
  eval₂Hom (Int.castRingHom _) fun v ↦ latticeForm (φ v.2)

def latticeIdeal {m N : ℕ} (φ : Fin (N + 1) → Fin m → K) :
    Ideal (MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ) :=
  RingHom.ker (latticeMap φ)

end

end GroundTheory.Heights₂.Heights
