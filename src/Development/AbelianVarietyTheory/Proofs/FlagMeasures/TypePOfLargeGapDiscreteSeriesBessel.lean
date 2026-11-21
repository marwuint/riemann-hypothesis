import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocDatCOfBesselOfW
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataTailBoundClosedFormLargeGaps
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundAtTermsOfLocalData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairCountBoundOfSiegelMassRatios
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAmplitudeFactorNonneg
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio

namespace GlobalTheory.TypeAsm.TopGap

theorem typeBound_of_gap :
    GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → Formalism.L2.SG.RowsPos.TypeP := by
  intro hH hBW

  have hAmp : GlobalTheory.TypeAsm.AmpP :=
    _root_.GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound (GlobalTheory.TypeAsm.locDatC_of_besselOfW hBW) (_root_.GlobalTheory.TypeAsm.TailTopGap.tailP_of_gap hH)

  have hPairs : GlobalTheory.TypeAsm.PairsP :=
    _root_.GlobalTheory.TypeAsm.pair_count_bound_of_siegel_mass GlobalTheory.Mass.MaxFormula.main GlobalTheory.Mass.siegelMassRatio_holds
  exact GlobalTheory.TypeAsm.typeBound_of_amplitude_pairs hAmp hPairs

end GlobalTheory.TypeAsm.TopGap
