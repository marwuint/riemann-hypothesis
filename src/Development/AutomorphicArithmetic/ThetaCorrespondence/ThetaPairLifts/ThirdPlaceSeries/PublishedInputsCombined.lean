import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityOfMinguez
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.DetNeZeroOfNearOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.Imports
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.RealPowerProductEqOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.LFrob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRank
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiTempered
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsPowValEqZpow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DepthZeroJacquetInjectiveOfAdmissible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RegularAlgebraicPurityOfClozel
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugationStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CohomologicalCsdTemperedOfSegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdan
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SOneRow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SPairs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeLAdicParameterAboveOfAlgebraicCharacterWDAl
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecT
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
namespace GlobalTheory.NRows.HypothesesBridge
theorem locComp_of_isRc_classMapD_cenLoc : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.MoyPrasadJacquetIso → GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.TemperedProductOfSquareIntegrable → GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.GelfandKazhdanDual → _root_.UpperTheory.GalS.PairUAlt → _root_.UpperTheory.One.M.Row → GlobalTheory.Published.ClozelPurity → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.AlgebraicCharacterWD → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.Zero.LLC.RecTExists → _root_.GlobalTheory.NRows.ThetaLocalInputsAlt := by
  intro hBZ hBern hGeo hTD hMP hJS hFin hTSI hESS hGK hGRP hCLGD hCP hCC hArt hChA hAlg hBerger hCheb hLL
  have hCSD := _root_.UpperTheory.GalS.bridgeStar_alt hGK
  exact
    { bz := hBZ
      bern := hBern
      geo := hGeo
      unl := GlobalTheory.TotDisjUnlinked.main hTD
      mp := GlobalTheory.depthZeroJacquetInjective_of_admissible hBZ hMP
      js := hJS
      fin := hFin
      gal := hCSD.2 hGRP
      car := _root_.UpperTheory.GalS.carU_of_finite_gl_recT hFin hLL (hCSD.1 hCLGD)
      clo := GlobalTheory.regularAlgebraicPurity_of_clozel hCP hCC
      art := hArt
      chA := hChA
      chP := _root_.GlobalTheory.heckeLAdicParameterAbove_of_algebraicCharacterWD_alt hAlg
      berger := hBerger
      cheb := hCheb }
end GlobalTheory.NRows.HypothesesBridge
end
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.published_inputs_combined_alt_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.MoyPrasadJacquetIso → GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.TemperedProductOfSquareIntegrable → GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.GelfandKazhdanDual → _root_.UpperTheory.GalS.PairUAlt → _root_.UpperTheory.One.M.Row → GlobalTheory.Published.ClozelPurity → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.AlgebraicCharacterWD → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.Zero.LLC.RecTExists → _root_.GlobalTheory.NRows.ThetaLocalInputsAlt := by
  exact @_root_.GlobalTheory.NRows.HypothesesBridge.locComp_of_isRc_classMapD_cenLoc
end
end
