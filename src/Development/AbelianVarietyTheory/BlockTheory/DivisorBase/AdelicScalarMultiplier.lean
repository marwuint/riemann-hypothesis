import Mathlib

open scoped TensorProduct NumberField
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarMultiplier

abbrev Af : Type := FiniteAdeleRing ℤ ℚ

def zHat : Subring Af where
  carrier := {a | ∀ v : HeightOneSpectrum ℤ, a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (v.adicCompletionIntegers ℚ)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (v.adicCompletionIntegers ℚ)
  neg_mem' ha v := neg_mem (ha v)

section Herm

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W]

def IsHermitian (h : LinearMap.BilinMap ℚ W E) : Prop :=
  (∀ (a : E) (x y : W), h (a • x) y = a * h x y) ∧
    ∀ x y : W, h y x = NumberField.IsCMField.complexConj E (h x y)

omit [NumberField.IsCMField E] in

def HasSignatureAt (h : LinearMap.BilinMap ℚ W E) (τ : E →+* ℂ) (p q : ℕ) : Prop :=
  ∃ b : Module.Basis (Fin p ⊕ Fin q) E W,
    (∀ i j, i ≠ j → h (b i) (b j) = 0) ∧
    (∀ i, 0 < (τ (h (b (Sum.inl i)) (b (Sum.inl i)))).re) ∧
    (∀ j, (τ (h (b (Sum.inr j)) (b (Sum.inr j)))).re < 0)

end Herm

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarMultiplier
