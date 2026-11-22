import Mathlib

noncomputable section

open scoped BigOperators

namespace Formalism.G0

def window (n i L : ℕ) : Finset ℕ :=
  (Finset.range L).image fun j => (i + j) % n

def CondA (n : ℕ) (T : Finset ℕ) (L₂ K : ℕ) : Prop :=
  ∀ i < n, (T ∩ window n i L₂).card ≤ K

def gaussBinom (q : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1)

def countBelow {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
    (A : Submodule F W) (j : ℕ) : ℕ :=
  Nat.card {U : Submodule F W // U ≤ A ∧ Module.finrank F U = j}

def SubspaceCount : Prop :=
  ∀ {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W] (k : ℕ),
    countBelow (⊤ : Submodule F W) k = gaussBinom (Fintype.card F) (Module.finrank F W) k

def TypeIIDown : Prop :=
  ∀ {F P Q : Type} [Field F] [Fintype F] [AddCommGroup P] [Module F P] [Finite P]
    [AddCommGroup Q] [Module F Q] [Finite Q] (f : P →ₗ[F] Q) (N g j : ℕ),
    Module.finrank F P = N → Module.finrank F Q = N + g →
    (Nat.card {U : Submodule F Q // LinearMap.range f ≤ U ∧ Module.finrank F U + j = N + g} : ℤ) =
      ∑ l ∈ Finset.range (j + 1),
        (Fintype.card F : ℤ) ^ ((j - l) * (g - l)) * gaussBinom (Fintype.card F) g l *
          countBelow (LinearMap.ker f) (j - l)

end Formalism.G0
