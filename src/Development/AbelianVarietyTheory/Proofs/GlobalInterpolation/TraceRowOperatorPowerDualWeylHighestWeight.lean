import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GlMatrixUnitPowCommutatorAndTraceCentral
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceGlMatrixUnitPowHighestWeightMod
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsRelationsDivPowBaseChang
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeight
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CommRowDivOfCommRowE

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rowDiv_smul_rat {r n : ℕ} (a b : Fin r) (k : ℕ) (c : ℚ)
    (f : MvPolynomial (Fin r × Fin n) ℚ) : rowDiv ℚ a b k (c • f) = c • rowDiv ℚ a b k f := by
  simp only [rowDiv, map_smul, Polynomial.coeff_smul]

theorem gel_hw_rat (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (k : ℕ) :
    gel ℚ N N k (hw ℚ le_rfl ν) = hcVal ℚ (fun i => (ν i : ℚ)) k • hw ℚ le_rfl ν := by
  have hrel := (_root_.GlobalTheory.Alc.rowOperators_main ℚ N N).1
  have hwt := _root_.GlobalTheory.Alc.rowE_rowWeight ℚ N N (rowNu (r := N) ν) (hw ℚ le_rfl ν) (hwRowWeight ℚ N N le_rfl ν hν)
  have hnu : ∀ a : Fin N, rowNu (r := N) ν a = ν a := by
    intro a
    simp [rowNu]
  have key := _root_.GlobalTheory.Alc.trace_pow_hw ℚ (MvPolynomial (Fin N × Fin N) ℚ) N (rowE ℚ N N) hrel ⊥
    (fun a b f hf => by
      rw [Submodule.mem_bot] at hf ⊢
      rw [hf, map_zero])
    (fun i => (ν i : ℚ)) (hw ℚ le_rfl ν)
    (fun a b hab => by
      rw [Submodule.mem_bot, (_root_.GlobalTheory.Alc.rowOperators_main ℚ N N).2.1 a b]
      exact hwRaise ℚ N N le_rfl ν a b 1 hab le_rfl)
    (fun a => by
      rw [Submodule.mem_bot, hwt.1 a, hnu a, sub_self]) k
  rw [Submodule.mem_bot, sub_eq_zero] at key
  exact key

theorem gel_dualWeyl_rat (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (k : ℕ)
    (f : MvPolynomial (Fin N × Fin N) ℚ) (hf : f ∈ dualWeyl ℚ N N ν) :
    gel ℚ N N k f = hcVal ℚ (fun i => (ν i : ℚ)) k • f := by
  set c : ℚ := hcVal ℚ (fun i => (ν i : ℚ)) k with hc
  have hrel := (_root_.GlobalTheory.Alc.rowOperators_main ℚ N N).1
  have hcomm : ∀ a b, gel ℚ N N k * rowE ℚ N N a b = rowE ℚ N N a b * gel ℚ N N k := fun a b =>
    ((_root_.GlobalTheory.Alc.glRel_pow_comm (Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) N (rowE ℚ N N) hrel k).2 a b).symm
  let M : Submodule ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
    dualWeyl ℚ N N ν ⊓ LinearMap.ker (gel ℚ N N k - c • (LinearMap.id))
  have hmem : ∀ g, g ∈ M ↔ g ∈ dualWeyl ℚ N N ν ∧ gel ℚ N N k g = c • g := by
    intro g
    simp [M, Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
  have hle : M ≤ dualWeyl ℚ N N ν := inf_le_left
  have hclosed : RowDivClosed M := by
    intro a b j g hg
    obtain ⟨hg1, hg2⟩ := (hmem g).1 hg
    refine (hmem _).2 ⟨rowDivStable ℚ N N ν a b j g hg1, ?_⟩
    rw [GlobalTheory.Alc.comm_rowDiv_of_comm_rowE N N (gel ℚ N N k) hcomm a b j g, hg2, rowDiv_smul_rat]
  have hhw : hw ℚ le_rfl ν ∈ M :=
    (hmem _).2 ⟨hwMem ℚ N N le_rfl ν hν, gel_hw_rat N ν hν k⟩
  have heq := closedEqNabla N N le_rfl ν hν M hle hclosed hhw
  exact ((hmem f).1 (heq ▸ hf)).2

end GlobalTheory.Alc
