import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionOverQOrDEqUnramifiedSupSqrt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtNegPrimeMemPadicCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtNegPrimeNotMemMaxUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StructureUnramifiedAdjoinSqrtNegPrime

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.LocalFieldsQD

theorem main : ∀ D : D7, EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D := by
  intro D
  refine ⟨fun i hi w hw => ?_, _root_.GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d D⟩
  obtain ⟨M, hM, y, hy, hK⟩ := _root_.GlobalTheory.HubLoc.kw_eq_unram_sup_sqrt D i hi w hw
  obtain ⟨-, -, hq8, hd16, -⟩ := D.host.hyp
  have h4 : D.nd.l i % 4 = 3 := by rcases hi with h | h <;> rw [h] <;> omega
  have h2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨e1, e2, e3, e4⟩ := _root_.GlobalTheory.SqrtNegL.structure_sqrt_neg (D.nd.l i) h2 (D.nbr i w hw).Kw M y hM hy
    (_root_.GlobalTheory.sqrt_neg_l_not_mem_Kur _ y hy) (_root_.GlobalTheory.sqrt_neg_l_mem_adjoin_roots_of_unity _ h4 y hy) hK
  exact ⟨⟨y, hy, e1⟩, e2, e3, e4⟩

end GlobalTheory.LocalFieldsQD
