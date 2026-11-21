import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecOfLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.OneTmulNeZeroOfDomain
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsNoetherianModelOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpansionTotal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

theorem globalFns : GlobalFnsSt :=
  GlobalFunctions.globalFns_of forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth

variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)

def toBK : DegPre.BF D F ⟶ DegPre.BF D F' := lift (fst _ _ ≫ θ) (snd _ _)

theorem toBK_fst : toBK θ D ≫ fst _ _ = fst _ _ ≫ θ := lift_fst _ _

theorem toBK_prB : toBK θ D ≫ DegPre.prB D F' = DegPre.prB D F := lift_snd _ _

theorem famφ_eq (α : D.X) (i : Fin 4) :
    DegPre.famφ D F α i = (toBK θ D).left ≫ DegPre.famφ D F' α i := by
  have e₀ := toBK_prB θ D
  have e₂ := comp_cP D (toBK θ D) α
  fin_cases i
  · exact congrArg (fun q => q.left) e₀.symm
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul (toBK θ D) (DegPre.prB D _) (cP D _ α)).trans
      (congrArg₂ (· * ·) e₀ e₂)).symm
  · exact congrArg (fun q => q.left) e₂.symm
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toBK θ D)).symm

theorem trF_toBK (mu : D.X) :
    DegPre.trF D F mu ≫ toBK θ D = toBK θ D ≫ DegPre.trF D F' mu := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, toBK_fst, Category.assoc, trF_eq, trF_eq, tr_fst, toBK_fst, ← Category.assoc, tr_fst]
  · refine (Category.assoc _ _ _).trans ((congrArg _ (toBK_prB θ D)).trans (Eq.trans ?_ (Category.assoc _ _ _).symm))
    rw [trF_eq, trF_eq, tr_pr]
    refine Eq.trans ?_ (congrArg (toBK θ D ≫ ·) (tr_pr D F' (cP D _ mu))).symm
    rw [MonObj.comp_mul, toBK_prB, comp_cP, comp_cP, comp_cP]

theorem exists_famPull (hθ : θ.left ≫ jFK (R := R) F' = jFK (R := R) F) (k : ℕ) (S : Fam D F' k) : ∃ S' : Fam D F k,
    ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (S'.s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := by
  have hp : (toBK θ D).left ≫ (DegPre.BF D F').hom =
      (DegPre.BF D F).hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) :=
    (Over.w _).trans ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm))
  let s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)) := fun α =>
    pullOver D.P.L (DegPre.famε k) hp (famφ_eq θ D α) (S.s α)
  have hs : ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := fun α Z r z J hJ =>
    sval_pullOver hp (famφ_eq θ D α) (S.s α) r hJ
  refine ⟨⟨s, fun mu α u hu hc => (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩, hs⟩
  have e₁ := (gen_fe globalFns k mu α).2 u hu hc _ (𝟙 _) y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F') globalFns k mu α
  have e₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (S.fe mu α u' hu' hc') _ (toBK θ D).left y J hJ
  rw [hv' u' hu' hc' _ (toBK θ D) y J hJ, ← Over.comp_left, ← trF_toBK, Over.comp_left] at e₂
  rw [Over.id_left] at e₁
  rw [hs _ _ _ y J hJ, hs _ _ _ y J hJ, Category.id_comp, Category.id_comp, e₂, e₁]
  have a : (toBK θ D ≫ fst _ _).left ≫ jFK (R := R) F' =
      (𝟙 (DegPre.BF D F) ≫ fst _ _).left ≫ jFK (R := R) F := by
    rw [toBK_fst, Category.id_comp, Over.comp_left, Category.assoc, hθ]
  rw [val_famMult _ hJ, val_famMult _ hJ, a, uVal, uVal, toBK_prB, comp_cP, comp_cP, comp_cP, comp_cP,
    Category.id_comp (DegPre.prB D F)]

end GlobalTheory.ExpansionTotal
