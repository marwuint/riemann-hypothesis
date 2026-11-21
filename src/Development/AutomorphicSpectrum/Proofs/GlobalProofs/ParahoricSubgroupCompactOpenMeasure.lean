import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Par

section Alg

variable {F : Type} [Field F]

def piIdeal (O : Subring F) (ϖ : F) : Ideal O where
  carrier := {x | ∃ o ∈ O, (x : F) = ϖ * o}
  add_mem' := by
    rintro a b ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
    exact ⟨x + y, O.add_mem hx hy, by simp [hax, hby, mul_add]⟩
  zero_mem' := ⟨0, O.zero_mem, by simp⟩
  smul_mem' := by
    rintro c a ⟨x, hx, hax⟩
    refine ⟨c * x, O.mul_mem c.2 hx, ?_⟩
    simp only [smul_eq_mul, Subring.coe_mul, hax]
    ring

def liftO {n : ℕ} (O : Subring F) (Z : Matrix (Fin n) (Fin n) F) (h : IsInt O Z) :
    Matrix (Fin n) (Fin n) O := fun i j => ⟨Z i j, h i j⟩

def red {n : ℕ} (O : Subring F) (ϖ : F) (Z : Matrix (Fin n) (Fin n) F) (h : IsInt O Z) :
    Matrix (Fin n) (Fin n) (O ⧸ piIdeal O ϖ) :=
  (liftO O Z h).map (Ideal.Quotient.mk (piIdeal O ϖ))

end Alg

end GlobalTheory.CompanionTheory.QL.Par
