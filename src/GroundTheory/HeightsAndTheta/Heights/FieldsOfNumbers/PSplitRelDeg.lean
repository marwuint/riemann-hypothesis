import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PfContractedHypothesesExample
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.HomFracDegZeroEqFunField
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameMultiHomog

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section SplitRelDeg

variable {F : Type u} [Field F] {K K' : Type} (j : K ↪ K') {ι' : K' → Type}
  (P' : Ideal (MRing ι' F)) [P'.IsPrime]

theorem contractFracMap_mk (f : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') f)) =
      algebraMap _ _ (Ideal.Quotient.mk P' (rename (blockIncl j ι') f)) := by
  simp [contractFracMap, contractQuot]
  rfl

end SplitRelDeg

end

end GroundTheory.Heights₂.Heights.FieldNumbers
