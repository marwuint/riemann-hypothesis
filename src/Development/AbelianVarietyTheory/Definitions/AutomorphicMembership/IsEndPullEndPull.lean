import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullback
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSymmetricLiftOddOrderLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MixCore

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommPairing (tval translT_fst)
open GlobalTheory.ThetaAct (sv sv_ext sv_add sv_smul translT_translT translT_one translT_snd translPt_one)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaLaw

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

section Group

variable {k : ℤ} {T : Over S}

theorem gen_ext {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u (𝟙 _) y J = val u' (𝟙 _) y J) : u = u' := by
  have e := sec_ext_val hM (s := genSec u hu) (s' := genSec u' hu') fun y J hJ => by
    rw [sval_genSec _ _ _ _ hJ, sval_genSec _ _ _ _ hJ, h y J hJ]
  cases u; cases u'
  exact congrArg _ (funext fun j => Units.ext (e j))

theorem ext {L : LB A.left} (hL : L.IsLB) {θ θ' : ThetaGrp A L k T} (h : θ.pt = θ'.pt)
    (hv : ∀ y J, Good L y J → tval θ (𝟙 _) y J = tval θ' (𝟙 _) y J) : θ = θ' := by
  obtain ⟨a, u, hu⟩ := θ
  obtain ⟨a', u', hu'⟩ := θ'
  obtain rfl : a = a' := h
  obtain rfl : u = u' := gen_ext hL hu hu' hv
  rfl

theorem exists_scalar {L : LB A.left} (hL : L.IsLB) (k : ℤ) (c : Γ(T.left, ⊤)ˣ) :
    ∃ θ : ThetaGrp A L k T, θ.pt = 1 ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ r z J = gm (r ≫ (fst T A).left) z ⊤ c := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![k, -k])
    (fun U _ f => by
      refine (Fintype.prod_empty _).trans ?_
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, translPt_one, mul_inv_cancel])
    (constGen A L c) (isGen_of_gm _ fun y j j' h h' => by
      obtain rfl : j = j' := Subsingleton.elim _ _
      rw [trF, Fintype.prod_empty, _root_.one_mul])
  exact ⟨⟨1, t, ht⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans (H1.val_constGen L c r z J)⟩

variable {L : RigLB A}

instance : One (ThetaGrp A L.L k T) := ⟨(exists_scalar L.isLB k 1).choose⟩

instance : Mul (ThetaGrp A L.L k T) := ⟨fun θ θ' => (ThetaAct.exists_mul L.isLB θ θ').choose⟩

instance : Inv (ThetaGrp A L.L k T) := ⟨fun θ => (ThetaAct.exists_inv L.isLB θ).choose⟩

theorem pt_one : (1 : ThetaGrp A L.L k T).pt = 1 := (exists_scalar L.isLB k 1).choose_spec.1

theorem pt_mul' (θ θ' : ThetaGrp A L.L k T) : (θ * θ').pt = θ'.pt * θ.pt :=
  (ThetaAct.exists_mul L.isLB θ θ').choose_spec.1

theorem pt_inv (θ : ThetaGrp A L.L k T) : θ⁻¹.pt = θ.pt⁻¹ := (ThetaAct.exists_inv L.isLB θ).choose_spec.1

section Val

variable {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.L.ι} (hJ : Good L.L z J)
include hJ

theorem tval_one : tval (1 : ThetaGrp A L.L k T) r z J = 1 :=
  ((exists_scalar L.isLB k 1).choose_spec.2 Z r z J hJ).trans (map_one _)

theorem tval_mul (θ θ' : ThetaGrp A L.L k T) :
    tval (θ * θ') r z J = tval θ r z J * tval θ' (r ≫ (translT A θ.pt).left) z J :=
  (ThetaAct.exists_mul L.isLB θ θ').choose_spec.2 Z r z J hJ

theorem tval_inv (θ : ThetaGrp A L.L k T) : tval θ⁻¹ r z J = (tval θ (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹ :=
  (ThetaAct.exists_inv L.isLB θ).choose_spec.2 Z r z J hJ

end Val

instance group : Group (ThetaGrp A L.L k T) :=
  Group.ofLeftAxioms
    (fun a b c => ext L.isLB (by simp only [pt_mul', _root_.mul_assoc]) fun y J hJ => by
      simp only [tval_mul _ _ hJ, pt_mul', Category.assoc, translT_translT, _root_.mul_assoc])
    (fun a => ext L.isLB (by rw [pt_mul', pt_one, _root_.mul_one]) fun y J hJ => by
      rw [tval_mul _ _ hJ, tval_one _ _ hJ, pt_one, translT_one, Category.comp_id, _root_.one_mul])
    (fun a => ext L.isLB (by rw [pt_mul', pt_inv, pt_one, mul_inv_cancel]) fun y J hJ => by
      rw [tval_mul _ _ hJ, tval_inv _ _ hJ, tval_one _ _ hJ, pt_inv, inv_mul_cancel])

variable (L k T)

variable {L k T}

variable [IsCommMonObj A]

theorem pt_mul (θ θ' : ThetaGrp A L.L k T) : (θ * θ').pt = θ.pt * θ'.pt := (pt_mul' θ θ').trans (mul_comm _ _)

variable (L k T) in

def ptHom : ThetaGrp A L.L k T →* (T ⟶ A) := MonoidHom.mk' ThetaGrp.pt pt_mul

end Group

end GlobalTheory.ThetaLaw
