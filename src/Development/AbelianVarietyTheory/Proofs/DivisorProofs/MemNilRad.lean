import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

noncomputable section

open Matrix
open scoped ContDiff

namespace GlobalTheory.TorFin

variable {n : ℕ} {G : Type} [Group G]

def IsUni (J u : Matrix (Fin n) (Fin n) ℂ) : Prop := uᴴ * J * u = J

def IsSkew (J Z : Matrix (Fin n) (Fin n) ℂ) : Prop := Zᴴ * J + J * Z = 0

def IsMulOn (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G) : Prop :=
  ∀ a b, IsUni J a → IsUni J b → s (a * b) = s a * s b

def lineOf (s : Matrix (Fin n) (Fin n) ℂ → G) (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : G := s (NormedSpace.exp (t • Z))

def smLoc (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G) : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ (k : ℕ) (Z : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, IsSkew J (Z i)) → ∀ g,
    ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => lineOf s (Z i) (t i)).prod)}
  add_mem' := fun hf hf' k Z hZ g => (hf k Z hZ g).add (hf' k Z hZ g)
  zero_mem' := fun _ _ _ _ => contDiff_const
  smul_mem' := fun c _ hf k Z hZ g => (hf k Z hZ g).const_smul c

theorem mem_smLoc {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} {f : G → ℂ} :
    f ∈ smLoc J s ↔ ∀ (k : ℕ) (Z : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, IsSkew J (Z i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => lineOf s (Z i) (t i)).prod) := Iff.rfl

def nilRad (J : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | Y *ᵥ x = 0 ∧ (star x ᵥ* J) ᵥ* Y = 0 ∧ ∀ v, (star x ᵥ* J) ⬝ᵥ v = 0 → ∃ a : ℂ, Y *ᵥ v = a • x}
  add_mem' := fun {Y Y'} h h' => ⟨by rw [add_mulVec, h.1, h'.1, add_zero], by rw [vecMul_add, h.2.1, h'.2.1, add_zero],
    fun v hv => let ⟨a, e⟩ := h.2.2 v hv; let ⟨a', e'⟩ := h'.2.2 v hv; ⟨a + a', by rw [add_mulVec, e, e', add_smul]⟩⟩
  zero_mem' := ⟨zero_mulVec _, vecMul_zero _, fun v _ => ⟨0, by simp⟩⟩
  smul_mem' := fun c Y h => ⟨by rw [smul_mulVec, h.1, smul_zero], by rw [vecMul_smul, h.2.1, smul_zero],
    fun v hv => let ⟨a, e⟩ := h.2.2 v hv; ⟨c * a, by rw [smul_mulVec, e, smul_smul]⟩⟩

theorem mem_nilRad {J Y : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℂ} : Y ∈ nilRad J x ↔
    Y *ᵥ x = 0 ∧ (star x ᵥ* J) ᵥ* Y = 0 ∧ ∀ v, (star x ᵥ* J) ⬝ᵥ v = 0 → ∃ a : ℂ, Y *ᵥ v = a • x := Iff.rfl

end GlobalTheory.TorFin

end
