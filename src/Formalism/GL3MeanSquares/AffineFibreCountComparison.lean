import Mathlib
import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound

namespace Formalism.HermitianLattices.RamifiedLatticeOperators

open Finset Matrix ComplexConjugate

def Fubini_orbits : Prop :=
  ∀ (Γ P Q V : Type) [Group Γ] [MulAction Γ P] [MulAction Γ Q] [AddCommGroup V] [Module ℚ V]
    (pr : P → Q) (fib : Q → Finset P) (Ψ : P → V) (RP : Finset P) (RQ : Finset Q),
    (∀ (γ : Γ) (p : P), pr (γ • p) = γ • pr p) → (∀ p y, p ∈ fib y ↔ pr p = y) →
    (∀ (γ : Γ) (p : P), Ψ (γ • p) = Ψ p) →
    (∀ y : Q, Finite (MulAction.stabilizer Γ y)) →
    (∀ p : P, ∃! r, r ∈ RP ∧ r ∈ MulAction.orbit Γ p) →
    (∀ y : Q, ∃! r, r ∈ RQ ∧ r ∈ MulAction.orbit Γ y) →
    ∑ p ∈ RP, ((Nat.card (MulAction.stabilizer Γ p) : ℚ))⁻¹ • Ψ p =
      ∑ y ∈ RQ, ((Nat.card (MulAction.stabilizer Γ y) : ℚ))⁻¹ • ∑ p ∈ fib y, Ψ p

def Count_orbits : Prop :=
  ∀ (Γ A B V : Type) [Group Γ] [MulAction Γ A] [MulAction Γ B] [AddCommGroup V] [Module ℚ V]
    (up : A → Finset B) (down : B → Finset A) (G : A → B → V) (RA : Finset A) (RB : Finset B),
    (∀ a b, b ∈ up a ↔ a ∈ down b) → (∀ (γ : Γ) a b, b ∈ up a → γ • b ∈ up (γ • a)) →
    (∀ (γ : Γ) a b, b ∈ up a → G (γ • a) (γ • b) = G a b) →
    (∀ a : A, Finite (MulAction.stabilizer Γ a)) → (∀ b : B, Finite (MulAction.stabilizer Γ b)) →
    (∀ a : A, ∃! r, r ∈ RA ∧ r ∈ MulAction.orbit Γ a) →
    (∀ b : B, ∃! r, r ∈ RB ∧ r ∈ MulAction.orbit Γ b) →
    ∑ a ∈ RA, ((Nat.card (MulAction.stabilizer Γ a) : ℚ))⁻¹ • ∑ b ∈ up a, G a b =
      ∑ b ∈ RB, ((Nat.card (MulAction.stabilizer Γ b) : ℚ))⁻¹ • ∑ a ∈ down b, G a b

def LemmaB'_length : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (ι : Type) [Fintype ι] (deg : ι → ℕ),
      Module.length R ((ι → R) ⧸
        (Submodule.pi Set.univ (fun i => Ideal.span {ϖ ^ deg i}) : Submodule R (ι → R))) =
        ((∑ i, deg i : ℕ) : ℕ∞)

end Formalism.HermitianLattices.RamifiedLatticeOperators
