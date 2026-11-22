import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift

open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise NNReal ENNReal

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair

section Objects
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ}

variable (k n) in

def flagSub (c i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) where
  carrier := {y | ∀ l : Fin c, i ≤ l.val → y (Sum.inr l) = 0}
  zero_mem' _ _ := rfl
  add_mem' h h' l hl := by simp [h l hl, h' l hl]
  smul_mem' s y h l hl := by simp [h l hl]

def interX (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Submodule 𝒪[k] (n → k) := L.comap (inX k n c)

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def InCoset (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (h₀ h : GL (n ⊕ Fin c) k) : Prop :=
  ∃ r ∈ R k n c 1, ∃ κ ∈ latStab L₀, h = r * h₀ * κ

variable [MeasurableSpace k] [BorelSpace k]

end Objects

section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (q : Unif k)

def OneOrbit : Prop :=
  (∀ (L₁ L₂ : Submodule 𝒪[k] (n → k)) (f₁ f₂ : n → k), IsGlue L₁ f₁ → IsGlue L₂ f₂ →
    ∃ g : GL n k, g • L₁ = L₂ ∧ g • f₁ - f₂ ∈ L₂) ∧
  ∀ (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (Q : Pair k n) (h₀ : GL (n ⊕ Fin c) k),
    h₀ • L₀ = gluedS q c Q.ker Q.vec → ∀ h : GL (n ⊕ Fin c) k,
      (∃ u ∈ N k n c 1, ∃ (L'' : Submodule 𝒪[k] (n → k)) (f'' : n → k), IsGlue L'' f'' ∧
        h • L₀ = u • gluedS q c L'' f'') ↔ InCoset L₀ h₀ h

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)

end Statements

end GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
