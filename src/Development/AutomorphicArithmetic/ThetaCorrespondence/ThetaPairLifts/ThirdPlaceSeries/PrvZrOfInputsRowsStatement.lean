import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvZrOfInputsRows
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedMultiplicity_of_inputs : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → _root_.GlobalTheory.NRows.PointConditions' D → SumRepresentations.ReducedMultiplicityStatement D := by
  exact @_root_.GlobalTheory.PtSt.reducedMultiplicity_of_rows'
end
