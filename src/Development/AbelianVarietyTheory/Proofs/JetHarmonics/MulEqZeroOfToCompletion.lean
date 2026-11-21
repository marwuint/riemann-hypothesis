import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ConjugatePlaceEigen
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct

namespace GlobalTheory.EigenLieCompare

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen GlobalTheory.HodgeTateCompare

section Local

open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems (Lie Cotangent)

variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
  [IsCommMonObj G] {R : Type} [CommRing R] (α : RingAct G R)

def eigSub (τ : R →+* O) : Submodule O (Lie G) where
  carrier := {x | ∀ a : R, (lieEquiv G x).1 ≫ α.act a = (lieEquiv G (τ a • x)).1}
  add_mem' := fun {x y} hx hy a => by
    haveI := α.hom a
    rw [smul_add, lieEquiv_add, lieEquiv_add, ← hx a, ← hy a, MonObj.mul_comp]
  zero_mem' := fun a => by
    haveI := α.hom a
    have h : (lieEquiv G 0).1 = 1 := by
      have := lieEquiv_add (G := G) 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    rw [smul_zero, h, MonObj.one_comp]
  smul_mem' := fun c x hx a => by
    rw [smul_comm, lieEquiv_smul, lieEquiv_smul c, ← hx a, Category.assoc]

def subEquiv (τ : R →+* O) : eigSub α τ ≃ LieEig α τ :=
  (lieEquiv G).subtypeEquiv fun x => forall_congr' fun a => by rw [lieEquiv_smul]

theorem subEquiv_val (τ : R →+* O) (x : eigSub α τ) :
    (subEquiv α τ x).1 = lieEquiv G x.1 := rfl

end Local

section Places

variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E]

theorem toPadic_apply (a : 𝓞 E) : toPadic p E a = (1 : ℤ_[p]) ⊗ₜ[ℤ] a := rfl

end Places

end GlobalTheory.EigenLieCompare
