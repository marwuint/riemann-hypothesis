import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexRationalTmulCoord
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AveragedSeriesFullRankOfComplexSpanGoodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsSpannedByThetaSeriesOfClassSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsClassSumsOfProjectedLiftRange
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalDatumSmallFieldFormHeckeScalarUnit

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.MainNotions.IntegralHeckeForms
open Formalism.IndefR.Links
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TieRank
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Target
open GlobalTheory.TwInputs GlobalTheory.SeriesTie Formalism.MainNotions

theorem faithful_serSide {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m)
    (b : Bool) : Faithful (Y.Z.rd i j b) :=
  realRd_faithful D X.Γ X.Pl0 X.I0 X.T X.A3 _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b (Y.Z.ν i j b)
    (Y.Z.scalar i j b).ne X.unif X.char.models.HW (Y.Z.vec j) ((_root_.GlobalTheory.TwUnit.isKsForm_and_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)

theorem rank_of_ties : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ i,
    BaseTup Y i → (∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
    FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  intro hP D X E Y i hB hR
  have hG : ∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t :=
    GlobalTheory.AdSpan.goodRangeAt X.R.toRealDat hP X.size X.char.lev X.char.grp.record X.char.fam X.char.models X.char.thP
  exact GlobalTheory.T.averaged_series_full_rank_of_complex_span_good D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.tie (faithful_serSide X Y) E i (fun j b => (Y.Z.rat (hR j b)).1)
    (fun j hj b a => Y.all i j hj b a) (_root_.GlobalTheory.TwInputs.spanGood_of_sumOnto D Y.Z.ρ Y.Z.good Y.Z.rd i (_root_.GlobalTheory.RankOnto.sumOnto_of_goodRange D X E Y hG i hB))

end Target

end GlobalTheory.TieRank

end
