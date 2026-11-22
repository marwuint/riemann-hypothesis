import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRangeOfCls
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ScalCompSpecMap
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Bdy

section Sec

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif I D A G)

def SecGK : Type :=
  SecOver (pullback.snd G.hom (jK R))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)))

instance : AddCommGroup (SecGK U) := inferInstanceAs (AddCommGroup (SecOver _ _))
instance : Module (FractionRing R) (SecGK U) := inferInstanceAs (Module (FractionRing R) (SecOver _ _))
instance : Module R (SecGK U) := Module.compHom _ (algebraMap R (FractionRing R))
instance : IsScalarTower R (FractionRing R) (SecGK U) :=
  ⟨fun a b s => by rw [Algebra.smul_def, mul_smul]; rfl⟩

end Sec

end GlobalTheory.LocM.Bdy
