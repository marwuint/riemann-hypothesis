import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpCell
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpTrans
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpBig
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpOrbPf
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
import Formalism.SharpRestriction.CuspSpanNormBounds.NearParameterGap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselFunctionBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.L2NormScaling
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbConvDDOfDecDD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiRegOf
import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZeroOfAe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FdegOfSchur
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeSS
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HzOfInWb
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.GapOfHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.NonzeroKFinite
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.FlipOneTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec
import Formalism.SharpRestriction.CuspSpanNormBounds.KFinOfLowUnitH
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv

namespace Formalism.L2.S.Pv.AmpFinal

open Formalism.MainNotions.S.Pv.LemmaJ

theorem rootCmp_of_parts (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt) : RootCmp :=
  rootCmp_of Formalism.L2.S.Pv.AmpCell.cell_representation Formalism.MainNotions.S.Pv.AmpTrans.amplitude_transport hRJ hRH hOQ hRA

theorem ampUnif_of_parts (hAO : AmpOrbU) (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt)
    (hNZ : AmpNZ) : AmpUnif :=
  ampUnif_of' hAO (rootCmp_of_parts hRJ hRH hOQ hRA) hNZ

end Formalism.L2.S.Pv.AmpFinal
