import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffQuadSer
import Formalism.GaussJetBounds.GaussJetProofs.NormDetLeOneOfEntries
import Formalism.GaussJetBounds.GaussJetProofs.FirstRowMinorDegreeLeOne
import Formalism.GaussJetBounds.StatementQ
import Formalism.GaussJetBounds.StatementP
import Formalism.GaussJetBounds.GaussJetProofs.GField
import Formalism.GaussJetBounds.GaussJetProofs.FJEval
import Formalism.GaussJetBounds.GaussJetProofs.Labels

universe u

namespace Formalism.DworkPowerSeriesWeights

theorem intOp : IntOp.{u} := by
  unfold IntOp
  intro K _ _ ι Th hTh P hP
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro κ _
  rw [mul_assoc, norm_mul]
  exact mul_le_one₀ (hP κ) (norm_nonneg _) (hTh κ)
end Formalism.DworkPowerSeriesWeights
