import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzRed

variable {R : Type} [CommRing R]

theorem val_longElt (n : ℕ) (i j : Fin n) :
    (longElt n R : Matrix (Fin n) (Fin n) R) i j = if j = i.rev then 1 else 0 := rfl

theorem val_invT (a : ℕ) (g : GL (Fin a) R) :
    ((GlobalTheory.CuspRep.invT a R g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) = ((g⁻¹ : GL (Fin a) R) : Matrix _ _ R)ᵀ :=
  rfl

theorem val_map {S : Type} [CommRing S] (f : R →+* S) {n : ℕ} (g : GL (Fin n) R) :
    (GeneralLinearGroup.map f g : Matrix (Fin n) (Fin n) S) = (g : Matrix (Fin n) (Fin n) R).map f := rfl

end DiscreteGroups.sglob.DzRed
