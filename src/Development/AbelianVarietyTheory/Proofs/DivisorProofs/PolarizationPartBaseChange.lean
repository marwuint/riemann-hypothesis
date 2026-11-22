import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtPelUnif

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PolPartPull

def oActIso {O : Type} [CommRing O] {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom]
    (a : OAct O A) : OAct O B where
  act x := e.inv ≫ a.act x ≫ e.hom
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one]; simp
  mul x y := by rw [a.mul]; simp
  add x y := by rw [a.add, MonObj.mul_comp, MonObj.comp_mul]

theorem pbMap_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

end GlobalTheory.PolPartPull

namespace GlobalTheory.PolPartPull

end GlobalTheory.PolPartPull
