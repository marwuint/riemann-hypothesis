import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDivisibleChainPrimaryTorsionGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleLocalConditionsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteLTorsionSelmerRankTwoAdjoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisibleOrdinarySelmerChainExistsIntegralRepresStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroOrdinaryClassOfCompatibleCocyclesModPowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousGaloisRepRankTwoTateDualOfOrdinaryNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualMatrixMemCoefRingOfNorma
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualExistsNoEigenvalueOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommutatorDetNonzero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualUpperTriangularDecomposiStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem gw_limit : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ¬ GrZero (dual1 W) A := by
  intro hL l _ Ω _ _ _ e S A W hW c hc H hGr
  have h1 := _root_.GlobalTheory.Ord2.DualCont.continuous_galoisRepRankTwoTateDual l Ω e S A W hW
  have h2 := _root_.GlobalTheory.Ord2.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm l Ω e S A W hW c hc
  have h3 := _root_.GlobalTheory.Ord2.galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt l Ω e S A W hW
  have h4 := _root_.GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified l Ω e S A W hW
  have h5 := GlobalTheory.T.galoisRepRankTwoTateDual_upperTriangular_decompositionGroup l Ω e S A W hW
  have hunb := GlobalTheory.T.exists_cocycle_local_conditions l Ω S A (dual1 W) c h2 h3 H
  have hfin := _root_.GlobalTheory.Ord2.finite_lTorsion_divSel hL l Ω S A (dual1 W) c hW.above h1 h2 h4
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.Ord2.DivChain.exists_divisible_chain l (DivSel c (dual1 W) S A) (divSel_torsion c (dual1 W) S A) hfin hunb
  obtain ⟨a, N, p1, p2, p3, p4, p5, p6, p7, p8⟩ := GlobalTheory.T.divisibleOrdinarySelmerChain_exists_integral_representatives l Ω S A (dual1 W) c h1 h2 h4 h5 x hx0 hx
  exact GlobalTheory.T.nonzero_ordinary_class_of_compatible_cocycles_mod_pow l Ω S A (dual1 W) c h1 h2 h3 a N p1 p2 p3 p4 p5 p6 p7 p8 hGr

end GlobalTheory.Ord2

end
