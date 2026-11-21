import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et

noncomputable section

namespace GlobalTheory.Et.CovChar.Trip

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

abbrev Tr : Scheme.{0} := pullback (pullback.snd f f) (pullback.fst f f)

def pr13 : Tr f ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _ ≫ pullback.snd f f) (by
    simp only [Category.assoc]
    rw [pullback.condition (f := f) (g := f), pullback.condition_assoc, pullback.condition (f := f) (g := f)])

@[reassoc (attr := simp)] theorem pr13_fst : pr13 f ≫ pullback.fst f f = pullback.fst _ _ ≫ pullback.fst f f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem pr13_snd : pr13 f ≫ pullback.snd f f = pullback.snd _ _ ≫ pullback.snd f f :=
  pullback.lift_snd _ _ _

variable (R : Type) [CommRing R]

end GlobalTheory.Et.CovChar.Trip
