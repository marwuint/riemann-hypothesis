import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat GlobalTheory.KernelNoTorsion GlobalTheory.HodgeTateTest GlobalTheory.PDiv GlobalTheory.SplitTorusPow
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusTateLie

section Torus

variable (C : Type) [Field C] {O : Type} [CommRing O] [Algebra O C] {X : Type} [AddCommGroup X]

def evalChar (χ : X) : (specO O O ⟶ splitTorus (Sp O) X) →* Cˣ :=
  (Units.map ((algebraMap O C).comp (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom).toMonoidHom).comp
    ((MonoidHom.eval (Multiplicative.ofAdd χ)).comp
      (splitTorusPointsEquiv (Sp O) X (specO O O)).toMonoidHom)

variable {C} {p : ℕ} [Fact p.Prime]

def cochar {J : Type} (b : Module.Basis J ℤ X) (j : J) : GmO O ⟶ splitTorus (Sp O) X :=
  torusMap (Sp O) ((AddEquiv.ulift (α := ℤ)).symm.toAddMonoidHom.comp (b.coord j).toAddMonoidHom)

instance {J : Type} (b : Module.Basis J ℤ X) (j : J) : IsMonHom (cochar (O := O) b j) :=
  isMonHom_torusMap _

end Torus

end GlobalTheory.TorusTateLie
