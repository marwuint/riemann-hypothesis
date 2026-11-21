import Mathlib

open Polynomial

noncomputable section

namespace PI.SqfLab

def Exc (g d ℓ : ℕ) : Prop := ℓ.Prime ∧ g ^ d < ℓ ^ (4 * padicValNat ℓ (g ^ d - 1))

def BB (N g : ℕ) : Set ℕ := {g} ∪ {ℓ | ∃ d, 1 ≤ d ∧ d ≤ N ∧ Exc g d ℓ}

def primeToPart (ℓ : ℕ) {M : Type*} [Monoid M] (x : M) : M :=
  x ^ (ℓ ^ (orderOf x).factorization ℓ *
    (((ℓ ^ (orderOf x).factorization ℓ : ℕ) :
      ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ))⁻¹).val)

abbrev Fbar (g : ℕ) [Fact g.Prime] : Type := AlgebraicClosure (ZMod g)

def IsLab (g r : ℕ) (f : (ZMod g)[X]) : Prop :=
  f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0

end PI.SqfLab
