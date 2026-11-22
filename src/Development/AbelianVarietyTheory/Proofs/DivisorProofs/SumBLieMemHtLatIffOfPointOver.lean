import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
open GlobalTheory.KernelNoTorsion
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.IndepPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P P' : Point p v O Λ}

def ptsHom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (T : Over S) :
    (T ⟶ A) →* (T ⟶ B) :=
  MonoidHom.mk' (fun x => x ≫ f) fun x y => MonObj.mul_comp x y _

variable (p) in

def tateIso {A B : Out.PolAV (Sp C)} (α : A.A ≅ B.A) [IsMonHom α.hom] : TateA A p ≃ₗ[ℤ_[p]] TateA B p :=
  LinearEquiv.ofLinearMap (Tate.map p (ptsHom α.hom _)) (Tate.map p (ptsHom α.inv _))
    (LinearMap.ext fun t => Tate.ext fun n => by
      change (t.lev n ≫ α.inv) ≫ α.hom = t.lev n
      simp)
    (LinearMap.ext fun t => Tate.ext fun n => by
      change (t.lev n ≫ α.hom) ≫ α.inv = t.lev n
      simp)

variable [IsAlgClosed C] [CharZero C]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]

variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (e : P.T ≃ₗ[ℤ_[p]] P'.T)

end GlobalTheory.CompHt.IndepPoint

namespace GlobalTheory.CompHt

end GlobalTheory.CompHt
