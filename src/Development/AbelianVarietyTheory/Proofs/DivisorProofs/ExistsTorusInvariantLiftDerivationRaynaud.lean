import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationLiftRaynaudPreimageAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageProjectionAbelianPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldExtendingAffineDerivation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightPreservingLiftOfBaseDerivation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPreservingVectorFieldOnSmallerPreimages
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.Heat.HxLift

theorem exists_invLift : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ d : Fld Y.H.left, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V.1) d ∧ ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  intro R _ _ Q O _ _ _ oa Y V D
  obtain ⟨δ₀, h0a, h0m, h0c⟩ := _root_.GlobalTheory.LiftDer.exists_lift_preimage R Q O oa Y V D
  obtain ⟨δ, ha, hm, hc, hw⟩ := _root_.GlobalTheory.WtLift.exists_isWt_lift R Q O oa Y V D δ₀ h0a h0m h0c
  obtain ⟨d, hd, hdU⟩ := _root_.GlobalTheory.DerFieldExt.exists_field Y.H.left _ (_root_.GlobalTheory.RayEv.Ray.isAffineOpen_preimage_q R Q O oa Y V) δ ha hm
  refine ⟨d, ⟨hd, fun O' hO' r => ?_⟩, ?_⟩
  · rw [← GlobalTheory.ZH.FormSec.res_constFn Y.H.hom hO' r, ← GlobalTheory.ZH.FormSec.res_constFn Y.H.hom hO' (D r),
      hd.2.2 _ _ hO' le_rfl, hdU, hc]
  · refine _root_.GlobalTheory.Heat.WtSub.isWt_field_of_le R Q O oa Y V d hd (fun α f hf => ?_)
    rw [hdU]
    exact hw α f hf

end GlobalTheory.Heat.HxLift
