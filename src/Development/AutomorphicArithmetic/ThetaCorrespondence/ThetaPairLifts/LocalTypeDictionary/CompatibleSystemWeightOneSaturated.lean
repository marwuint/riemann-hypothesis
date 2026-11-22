import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDataExtendLargerFieldsOfHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasBareOfHasPk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstructionStartingChoicesOfFineAdelicData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedAdelicDataSaturatedOverFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsFromPrintedInputs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsOfMultiplicityEqual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineAdelicDatumOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HypA
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityCoverHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsBareFormOfSaturation

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
noncomputable section
namespace GlobalTheory.HeightCounting.Up
theorem weightOne_saturated_of_hypotheses : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState := fun hA hH =>
  _root_.GlobalTheory.T.exists_bare_form_of_saturation hA hH (_root_.GlobalTheory.Mem.R3.Rw.datExt0_of_hypotheses hH.cover hA.a5 hA.a6 hA.a7 hA.a8 hA.a9 hA.a10)
end GlobalTheory.HeightCounting.Up
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleSystem_weightOne_saturated : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.weightOne_saturated_of_hypotheses | exact _root_.GlobalTheory.HeightCounting.Up.weightOne_saturated_of_hypotheses | (intros; apply _root_.GlobalTheory.HeightCounting.Up.weightOne_saturated_of_hypotheses <;> assumption)
end
