import Mathlib
import Formalism.PeriodIntegrals.IsoDet

noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs

section Gen

variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]

end Gen

section Loc

variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
variable (p : Ideal R) [p.IsPrime]

theorem mem_locP {A : Submodule R W} {x : W} :
    x ∈ localization₂ p A ↔ ∃ s ∈ p.primeCompl, s • x ∈ A := Iff.rfl

end Loc

end PI.IsoDetW.Loc
