import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

namespace GlobalTheory.CompanionTheory.Ar.HS

open MvPolynomial NumberField GroundTheory.Heights₂.Heights

noncomputable section

section Forms
variable {R : Type*} [CommRing R] {k D N n : ℕ}

def pull (w : Fin n → Fin N → R) (f : MvPolynomial (Fin k × Fin N) R) :
    MvPolynomial (Fin k × Fin n) R :=
  bind₁ (fun ij => ∑ a, C (w a ij.2) * X (ij.1, a)) f

end Forms

structure ChowData (F : Type) [Field F] [NumberField F] (D N n δ : ℕ) where

  I : Ideal (MvPolynomial (Fin N) F)
  projPrime : IsProjPrime I
  nondeg : ∀ u : Fin N → F, linForm u ∈ I → u = 0
  one_le_D : 1 ≤ D

  f : MvPolynomial (Fin (D + 1) × Fin N) F
  chow : IsChowForm I (D + 1) f
  homog : IsMultiHomog δ f

  w : Fin n → Fin N → F
  span_top : Submodule.span F (Set.range w) = ⊤
  int_stable : ∀ (c : 𝓞 F) (a : Fin n), (c : F) • w a ∈ Submodule.span ℤ (Set.range w)

  H : ArchData F N

  Λ : ℝ
  one_le_Λ : 1 ≤ Λ
  w_le : ∀ (a : Fin n) (σ : F →+* ℂ), (H.normAt σ).norm (fun j => σ (w a j)) ≤ Λ

  θ : Fin N → F
  θ_ne : θ ≠ 0

namespace ChowData
end ChowData

end

end GlobalTheory.CompanionTheory.Ar.HS
