import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzRed

variable {R : Type} [CommRing R]

theorem val_map {S : Type} [CommRing S] (f : R →+* S) {n : ℕ} (g : GL (Fin n) R) :
    (GeneralLinearGroup.map f g : Matrix (Fin n) (Fin n) S) = (g : Matrix (Fin n) (Fin n) R).map f := rfl

end DiscreteGroups.sglob.DzRed
