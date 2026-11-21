import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetSubPf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NuAlgLeOfCharts
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsoIntegralModelsMatchingLieBases
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionBaseChange
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFramesCoefficientRingBaseChange
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFrameGCoefficientRingBaseChange
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CubeFramesMoveToPullbackTriple
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionIffPullback
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameFirstPartialLawIffPullback
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSecondPartialLawIffPullback
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSymmetryIffPullback
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointSeriesFramesPullback
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNMap
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsCanonGaugeMapFB
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsRawChartBaseChangeJetPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.DepthExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem grp_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 _) (𝟙 _) :=
  ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun _ x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
      (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm⟩

section Tangent
variable {V V' : Type} [CommRing V] [CommRing V']

theorem comb_iff (t : SAB H (Sp V)) {m : ℕ} (v : Fin m → (epsR V ⟶ t.G)) (cf : Fin m → V) (w : epsR V ⟶ t.G) :
    IsLieComb cf v w ↔ IsCombAtG t (𝟙 _) (fun i => (v i).left) cf w.left := by
  simp only [Chart.comb_push (grp_id t.G), Category.comp_id]
  exact Iff.rfl

theorem tan_iff (t : SAB H (Sp V)) (w : epsR V ⟶ t.G) : IsTangent w ↔ IsTanAtG t (𝟙 _) w.left := by
  simp only [Chart.tan_push (grp_id t.G), Category.comp_id]
  exact ⟨fun h => ⟨(Over.w w).trans (Category.comp_id _).symm, h⟩, fun h => h.2⟩

variable (ψ : V →+* V') {t : SAB H (Sp V)} {t' : SAB H (Sp V')} (mp : SABMap t' t (spMap ψ))

end Tangent

end GlobalTheory.DepthExt
