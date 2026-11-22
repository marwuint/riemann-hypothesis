import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EmbeddingPermutesLetters
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtTransInvHolds
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

end Formalism.MainNotions.Ext

open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

theorem discr_K {R : Ranks} (H : Host R) : discr H.K = -(H.d : ℤ) := by
  obtain ⟨-, hdp, -, hd16, -⟩ := H.hyp
  have hm : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ H.sqd
  have hx : (⟨H.sqd, hm⟩ : H.K) ^ 2 = ((-(H.d : ℤ) : ℤ) : H.K) := by
    apply Subtype.ext
    push_cast
    exact H.sqd_sq
  refine Formalism.HF.P.quadDiscr_ne_one H.K (-(H.d : ℤ)) _ hx ?_ ?_ ?_ ?_
  · have key : @IntermediateField.adjoin ℚ _ H.K _ H.K.algebra' {⟨H.sqd, hm⟩} = ⊤ := by
      apply IntermediateField.map_injective (IntermediateField.val H.K)
      rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
        Set.image_singleton]
      first
      | rfl
      | (simp only [IntermediateField.val_mk]; rfl)
      | simp [Formalism.HC.HostRaw.K]
    convert key
    all_goals first
      | exact Subsingleton.elim _ _
      | (apply Algebra.algebra_ext; intro r; simp [Algebra.algebraMap_eq_smul_one])
  · exact Int.squarefree_natAbs.mp (by simpa using hdp.prime.squarefree)
  · omega
  · omega

end Formalism.MainNotions.Ext
