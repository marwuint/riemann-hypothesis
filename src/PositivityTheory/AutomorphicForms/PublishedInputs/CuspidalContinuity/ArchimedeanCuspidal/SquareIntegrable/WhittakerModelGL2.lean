import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3

section Mat

variable {R : Type*} [CommRing R]

def uni2 (x : R) : GL (Fin 2) R :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def dg2 (a b : Rˣ) : GL (Fin 2) R :=
  ⟨!![(a : R), 0; 0, b], !![((a⁻¹ : Rˣ) : R), 0; 0, (b⁻¹ : Rˣ)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def w0 : GL (Fin 2) R :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

end Mat

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def W2 (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ) (g : GL (Fin 2) F) : ℂ :=
  ((μ₂ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (1 / 2) *
    ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      (∫ x, φ (![(h : F), h * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ) ∂multHaar F

end Ad3
