import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights

universe u v

noncomputable section

theorem finrank_submodule_eq {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    (F : Submodule R M) (hF : ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x ∈ F) :
    Module.finrank R F = Module.finrank R M := by
  have h0 : Module.rank R (M ⧸ F) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨x, rfl⟩ := F.mkQ_surjective x
    obtain ⟨a, ha, hax⟩ := hF x
    refine ⟨a, ha, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hax
  have h := rank_quotient_add_rank_of_isDomain F
  rw [h0, zero_add] at h
  simp only [Module.finrank, h]

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
