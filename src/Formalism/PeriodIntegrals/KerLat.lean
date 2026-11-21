import Mathlib

noncomputable section
open NumberField

namespace PI.KerLat

def PerPair : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Module.finrank ℚ K = 2 → (∃ k : K, (φ k).im ≠ 0) → cc ≠ ⊥ → δ ≠ 0 →
      ∃ L : PeriodPair, L.lattice.toAddSubgroup = AddSubgroup.closure {w : ℂ | ∃ c ∈ cc, w = δ * φ (c : K)}

end PI.KerLat
