import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfCountAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumCountBoundLargeData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineCountOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorCountBoundOfCosetDepthBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKCosetCountFormula

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
namespace GlobalTheory.SumCount
theorem archimedean_sum_count_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DepthK → InfCountK := fun hP hD =>
  infCountK_of _root_.GlobalTheory.SumCount.DataCount.dataK (_root_.GlobalTheory.T.theta_kCoset_count_formula hP) (GlobalTheory.T.pureTensorCountBound_of_cosetDepthBound hD)
end GlobalTheory.SumCount
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_count_bound_archimedean : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DepthK → InfCountK := by
  first | exact @_root_.GlobalTheory.SumCount.archimedean_sum_count_bound | exact _root_.GlobalTheory.SumCount.archimedean_sum_count_bound | (intros; apply _root_.GlobalTheory.SumCount.archimedean_sum_count_bound <;> assumption)
end
