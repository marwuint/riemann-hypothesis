import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstantOneNotCuspidalOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Formalism.LocalRingCardinality.SpanPowerMembership
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

noncomputable section

open scoped ComplexConjugate NNReal ENNReal
open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Cusp GlobalTheory.MixModel
open GlobalTheory.Mem.Th (InfF CptF)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (delta swSec sZero IsKFinVec ThetaClause DoublingIso)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RallisIP.Model

variable {D : D7} {A B : HSp D}

theorem vol_pos (mH : Measure (GA D B)) [mH.IsHaarMeasure] : 0 < (autMeasure B mH).real Set.univ :=
  ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 (NeZero.ne _)) (measure_ne_top _ _)

variable {ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)} {m : Measure (GA D A)}

end GlobalTheory.RallisIP.Model

end
