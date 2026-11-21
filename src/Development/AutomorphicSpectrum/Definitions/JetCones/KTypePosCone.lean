import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.ConstantCoeffRhoOneCanonMonomial
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.DSInfCharCap

open GroundTheory.Automorphic.HarishChandra Finset

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.CompanionTheory.DS

abbrev Pr (n : ℕ) := Fin n × Fin n

abbrev Coch (n : ℕ) (X : Type) := Finset (Pr n) → X

variable {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]

def sgn (S : Finset (Pr n)) (α : Pr n) : ℂ := (-1) ^ (S.filter fun β => toLex β < toLex α).card

def wedge (α : Pr n) : Module.End ℂ (Coch n X) :=
  LinearMap.pi fun S => if α ∈ S then sgn S α • LinearMap.proj (S.erase α) else 0

def contr (α : Pr n) : Module.End ℂ (Coch n X) :=
  LinearMap.pi fun S => if α ∈ S then 0 else sgn S α • LinearMap.proj (insert α S)

def ptw (T : Module.End ℂ X) : Module.End ℂ (Coch n X) := T.compLeft (Finset (Pr n))

def dC (Φ : Finset (Pr n)) (x : Pr n → Module.End ℂ X) : Module.End ℂ (Coch n X) :=
  ∑ α ∈ Φ, wedge α * ptw (x α) -
    ∑ α ∈ Φ, ∑ β ∈ Φ.filter (fun β => α.2 = β.1), wedge α * wedge β * contr (α.1, β.2)

def Exact (Φ : Finset (Pr n)) (x : Pr n → Module.End ℂ X) (j : ℕ) (f : Coch n X) : Prop :=
  ∃ η : Coch n X, (∀ S, η S ≠ 0 → S ⊆ Φ ∧ S.card + 1 = j) ∧ dC Φ x η = f

def DSUnique : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    PI.UpqRep.IsHCParam lam → PI.UpqRep.IsDS ε lam σ → PI.UpqRep.IsDS ε lam σ' → PI.UpqRep.IsEquiv ε σ' σ

end GlobalTheory.CompanionTheory.DS
