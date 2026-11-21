import Mathlib
import Formalism.PeriodIntegrals.IsoDet

noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs

section Gen

variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]

def relative₂ (X Z : Submodule R W) : ℕ∞ := Module.length R (Z ⧸ X.comap Z.subtype)

end Gen

section Loc

variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
variable (p : Ideal R) [p.IsPrime]

theorem mem_locP {A : Submodule R W} {x : W} :
    x ∈ localization₂ p A ↔ ∃ s ∈ p.primeCompl, s • x ∈ A := Iff.rfl

theorem lidx_eq (A B : Submodule R W) :
    lidx p A B = ((relative₂ (localization₂ p (A ⊓ B)) (localization₂ p A)).toNat : ℤ) - (relative₂ (localization₂ p (A ⊓ B)) (localization₂ p B)).toNat :=
  rfl

end Loc

end PI.IsoDetW.Loc
