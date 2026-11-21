import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AltPullApply

noncomputable section

namespace GlobalTheory.KS

open CategoryTheory

variable {Γ : Type} [Group Γ] {L : Type} [AddCommGroup L]

variable {Γ' : Type} [Group Γ'] {L' : Type} [AddCommGroup L']

variable (E : Type) [Field E]

structure Asph (Y : Type) [TopologicalSpace Y] where
  n : ℕ
  G : Fin n → Type
  [grp : ∀ i, Group (G i)]
  X : Fin n → Type
  [top : ∀ i, TopologicalSpace (X i)]
  [act : ∀ i, MulAction (G i) (X i)]
  contr : ∀ i, ContractibleSpace (X i)
  π : ∀ i, C(X i, Y)
  isOpen : ∀ i, IsOpen (Set.range (π i))
  cov : ∀ i, IsQuotientCoveringMap (Set.rangeFactorization (π i)) (G i)
  disj : Pairwise fun i j => Disjoint (Set.range (π i)) (Set.range (π j))
  cover : ∀ y, ∃ i, y ∈ Set.range (π i)

attribute [instance] Asph.grp Asph.top Asph.act

structure Asph.Lift {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y'] (K' : Asph Y') (K : Asph Y) (f : C(Y', Y)) where
  κ : Fin K'.n → Fin K.n
  α : ∀ i, K'.G i →* K.G (κ i)
  lift : ∀ i, C(K'.X i, K.X (κ i))
  equiv : ∀ i (g : K'.G i) x, lift i (g • x) = α i g • lift i x
  comm : ∀ i x, K.π (κ i) (lift i x) = f (K'.π i x)

end GlobalTheory.KS
