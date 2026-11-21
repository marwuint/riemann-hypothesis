import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntermediateFieldOfForallComplexAutFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZero
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.sqProd_sq_mem_and_stable : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t →
    sqProd p L t ^ 2 ∈ F ∧ (sqProd p L t ∈ F → Stable L F (sqPt p t)) := by
  intro p F L t hp h4 h3 hD
  refine ⟨?_, ?_⟩
  · apply _root_.GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed F
    intro σ hσ
    rw [map_pow]
    rcases _root_.GlobalTheory.SqConj.sqProd_conj p F L t hp h4 h3 hD σ hσ with ⟨h, _⟩ | h
    · rw [h]
    · rw [h, neg_sq]
  · intro hmem σ hσ
    rcases _root_.GlobalTheory.SqConj.sqProd_conj p F L t hp h4 h3 hD σ hσ with ⟨_, he⟩ | h
    · exact he
    · exfalso
      have hne := (_root_.GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero p F L t hp h4 h3 hD).2
      have hfix : σ (sqProd p L t) = sqProd p L t := hσ _ hmem
      rw [hfix] at h
      have h2 : (2 : ℂ) * sqProd p L t = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2 with h2 | h2
      · norm_num at h2
      · exact hne h2
