import Mathlib
import Formalism.DistinguishedUnitIdeals.FrobeniusDiffBijective
import Formalism.DistinguishedUnitIdeals.ExistsConstOfInvariantMod

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

def FactVval {O : Type} [CommRing O] (u : Oˣ) (ℓ : ℕ) : Prop :=
  ∀ m : ℤ, m ≠ 0 → ∃ ε : Oˣ, 1 - ((u ^ m : Oˣ) : O) = (ε : O) * (ℓ : O) ^ (1 + padicValInt ℓ m)

def FactVvalOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (ℓ : ℕ) (u x : Oˣ), ℓ.Prime → 3 ≤ ℓ →
    ¬ IsUnit (ℓ : O) → (u : O) = 1 + (ℓ : O) * (x : O) → FactVval u ℓ

def FactVOf : Prop :=
  ∀ (O LL Ks Δ : Type) [CommRing O] [Field LL] [Algebra O LL] [CommRing Ks] [Algebra LL Ks]
    (Lev : G.Level LL Ks Δ) (u : Oˣ) (ℓ : ℕ), (Lev.u : LL) = algebraMap O LL (u : O) →
    (ℓ : LL) ≠ 0 → FactVval u ℓ → Lev.FactV

def kapExp (ℓ E : ℕ) (JS : Finset ℤ) : ℕ :=
  E + ∑ i ∈ JS.erase 0, (1 + E + padicValInt ℓ i)

def PPvalOf : Prop :=
  ∀ (O : Type) [CommRing O] (u : Oˣ) (ℓ E kap : ℕ) (JS JS' : Finset ℤ), ℓ.Prime → FactVval u ℓ →
    2 * E + ∑ i ∈ JS.erase 0, (1 + E + padicValInt ℓ i) +
      ∑ i ∈ JS'.erase 0, (1 + E + padicValInt ℓ i) ≤ 2 * kap →
    PPval ℓ kap (G.PPoly u ℓ E JS) (G.PPoly u ℓ E JS')

def Base.PhiFree {O : Type} [CommRing O] (B : Base O) (k : ℕ) : Prop :=
  ∃ (r : ℕ) (b : Fin r → PowerSeries O),
    (∀ a : PowerSeries O, ∃ a' : Fin r → PowerSeries O, a = ∑ t, b t * (⇑B.φ)^[k] (a' t)) ∧
    ∀ a' : Fin r → PowerSeries O, ∑ t, b t * (⇑B.φ)^[k] (a' t) = 0 → ∀ t, a' t = 0

end Formalism.ExponentWindows.E
