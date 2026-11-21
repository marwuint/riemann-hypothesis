import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

noncomputable section

open Polynomial

namespace Formalism.L2.NG

section lab

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {p : ℕ} [Fact p.Prime]

def LevelOf (f : (ZMod p)[X]) (d : ℕ) : Prop := 0 < d ∧ ∀ x ∈ Formalism.CyclotomicNorms.rootsBar f, x ^ (p ^ d - 1) = 1

variable {A : ValuationSubring Ω} {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {ζ : ℕ → Formalism.CyclotomicNorms.Fbar p}
  {teich : Formalism.CyclotomicNorms.Fbar p →* ℂ} {I : Set (Ω ≃ₐ[E] Ω)} {n : ℕ} {P : (Ω ≃ₐ[E] Ω) → ℂ[X]} {f f' : (ZMod p)[X]}

end lab

end Formalism.L2.NG
