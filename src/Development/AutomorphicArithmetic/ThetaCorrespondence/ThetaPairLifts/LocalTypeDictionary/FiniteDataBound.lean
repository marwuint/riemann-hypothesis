import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDataBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
namespace GlobalTheory.FunDat
end GlobalTheory.FunDat
noncomputable section
namespace GlobalTheory.FunDat
theorem finDatK_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinDatK := fun _ => finDatK_of GlobalTheory.T.flips_loss_bounded_at_exceptional_places _root_.GlobalTheory.UnfoldLoss.unfold_loss
end GlobalTheory.FunDat
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finDatK_of_theta_inputs : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinDatK := by
  first | exact @_root_.GlobalTheory.FunDat.finDatK_alt | exact _root_.GlobalTheory.FunDat.finDatK_alt | (intros; apply _root_.GlobalTheory.FunDat.finDatK_alt <;> assumption)
end
