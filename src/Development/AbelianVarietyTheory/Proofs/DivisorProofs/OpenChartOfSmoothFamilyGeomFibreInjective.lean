import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyParamInjectiveOfGeomFiberInjecti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoLiftSmallArtinExtensions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothInjectiveFamilyLiftsSmallArtinian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyOpenChartAffineFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyChartAffineOfChartFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyChartOfAffineParameters

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCrit

theorem openChart : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom → Fam A M → FibInj A M → IsChart A M := by
  intro R _ _ A _ g hA hAg U M hU hM hF
  have hUf : LocallyOfFiniteType U.hom := by
    haveI := hU
    haveI : Smooth U.hom := SmoothOfRelativeDimension.smooth g _
    infer_instance
  have hI : Inj A M := _root_.GlobalTheory.DualInj.inj_of_fibInj R A hA U M hUf hM hF
  refine ⟨hM, hI, ?_⟩
  intro T N hN
  refine _root_.GlobalTheory.DualCon.chartAt_of_affine (Sp R) A hA U M hM hI ?_ T N hN
  intro T _ N hN
  refine _root_.GlobalTheory.DualApprox.chartAt_of_finiteType R A hA U M hM ?_ T N hN
  intro T _ hT N hN
  exact _root_.GlobalTheory.DualCon.chartAt_of_lifting R A hA U M hUf hM hI (fun f _ _ _ h => _root_.GlobalTheory.ArtinOpen.isOpenImmersion_of_lift f h) T hT N hN
    (_root_.GlobalTheory.DualCon.same_lift_small R A g hA hAg U M hU hM hI T N hN)

end GlobalTheory.ChartCrit
