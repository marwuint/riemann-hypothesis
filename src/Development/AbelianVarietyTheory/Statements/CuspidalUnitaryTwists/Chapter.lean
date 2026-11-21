import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

open UpperTheory.V.Af

def mes (k l : ℕ) {N : ℕ} (θ θ' : DirichletCharacter ℂ N) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (m : ℕ) (f : ZMod (l ^ m) → ℂ) : ℂ :=
  val B c l α m (Zs k l (ch θ) (hat θ') (quo f))

structure Meas {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e : ℕ) {N : ℕ} (θ θ' : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ l) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (v : ℂ) : Prop where
  compat : ∀ m : ℕ, 1 ≤ m → ∀ (f : ZMod (l ^ m) → ℂ) (f' : ZMod (l ^ (m + 1)) → ℂ), (∀ x, f (-x) = θ (-1) * f x) →
    (∀ x : ℕ, f' x = f x) → mes (2 * e + 1) l θ θ' α B c (m + 1) f' = mes (2 * e + 1) l θ θ' α B c m f
  bound : ∃ C : ℝ, ∀ (m : ℕ) (f : ZMod (l ^ m) → ℂ) (δ : ℝ), 0 ≤ δ → (∀ x, ‖ι.symm (f x)‖ ≤ δ) →
    ‖ι.symm (mes (2 * e + 1) l θ θ' α B c m f)‖ ≤ C * δ
  field : ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ (m : ℕ) (f : ZMod (l ^ m) → ℂ)
    (E' : IntermediateField ℚ_[l] (PadicAlgCl l)), E ≤ E' → (∀ x, ι.symm (f x) ∈ E') → ι.symm (mes (2 * e + 1) l θ θ' α B c m f) ∈ E'
  interp : ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ (f : ZMod (l ^ m) → ℂ) (δ : ℝ), 0 ≤ δ → (∀ x, f (-x) = θ (-1) * f x) →
    (∀ x y : ℕ, ¬ l ∣ x → ¬ l ∣ y → ‖ι.symm (quo f x y - ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)‖ ≤ δ) →
    ‖ι.symm (mes (2 * e + 1) l θ θ' α B c m f - v)‖ ≤ C * δ

end GlobalTheory.EisM

end
