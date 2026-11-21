import Mathlib

noncomputable section

open PowerSeries

namespace GlobalTheory.FOM

def resRed (Ob R : Type*) [CommRing Ob] [IsLocalRing Ob] [CommRing R] [IsLocalRing R] [Algebra Ob R]
    [IsLocalHom (algebraMap Ob R)]
    (hb : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap Ob R))) :
    R →+* IsLocalRing.ResidueField Ob :=
  (RingEquiv.ofBijective _ hb).symm.toRingHom.comp (IsLocalRing.residue R)

end GlobalTheory.FOM
