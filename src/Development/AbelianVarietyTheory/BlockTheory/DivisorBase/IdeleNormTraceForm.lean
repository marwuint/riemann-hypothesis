import Mathlib

open NumberField IsDedekindDomain TensorProduct

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IdeleNormTraceForm

abbrev Af : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

def Zhat : Subring Af where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {a b} ha hb v => (v.adicCompletionIntegers ℚ).mul_mem _ _ (ha v) (hb v)
  one_mem' := fun v => (v.adicCompletionIntegers ℚ).one_mem
  add_mem' := fun {a b} ha hb v => (v.adicCompletionIntegers ℚ).add_mem _ _ (ha v) (hb v)
  zero_mem' := fun v => (v.adicCompletionIntegers ℚ).zero_mem
  neg_mem' := fun {a} ha v => (v.adicCompletionIntegers ℚ).neg_mem _ (ha v)

section Groups

variable (E : Type) [Field E] [NumberField E]
variable {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]

def IsHermitian [IsCMField E] (h : W →ₗ[ℚ] W →ₗ[ℚ] E) : Prop :=
  (∀ (a : E) (x y : W), h (a • x) y = a * h x y) ∧
    ∀ x y : W, h y x = IsCMField.complexConj E (h x y)

def HasSignature (h : W →ₗ[ℚ] W →ₗ[ℚ] E) (p q' : ℕ) : Prop :=
  ∀ τ : E →+* ℂ, ∃ b : Module.Basis (Fin p ⊕ Fin q') E W,
    (∀ i j, i ≠ j → h (b i) (b j) = 0) ∧
    (∀ i, 0 < (τ (h (b (Sum.inl i)) (b (Sum.inl i)))).re) ∧
    (∀ i, (τ (h (b (Sum.inr i)) (b (Sum.inr i)))).re < 0)

variable [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

end Groups

end GlobalTheory.IndefiniteRowSideFullHecke.IdeleNormTraceForm
