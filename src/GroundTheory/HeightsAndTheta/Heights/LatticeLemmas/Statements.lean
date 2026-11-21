import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsExamples
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
open GroundTheory.Heights₂.Heights

universe u v w

noncomputable section

def BaseChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type w) [Field L] [NumberField L] [Algebra K L]
    (M : HermitianBundle.{v} K), (M.baseChange L).deg = M.deg

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
