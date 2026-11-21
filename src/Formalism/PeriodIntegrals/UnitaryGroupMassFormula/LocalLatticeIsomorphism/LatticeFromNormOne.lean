import Mathlib
import Formalism.PeriodIntegrals.KerIso

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW

def Rp (K : Type) [Field K] [NumberField K] (p : ℕ) (x : K) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) * x ∈ (algebraMap (𝓞 K) K).range

def hf {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v w : ι → K) : K :=
  ∑ i, v i * c (w i)

def Unimod (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type} [Fintype ι]
    (L : Set (ι → K)) : Prop :=
  ∀ v, v ∈ L ↔ ∀ w ∈ L, Rp K p (hf c v w)

end PI.KLW
