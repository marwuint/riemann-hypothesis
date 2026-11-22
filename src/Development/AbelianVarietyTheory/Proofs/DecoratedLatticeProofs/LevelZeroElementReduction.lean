import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaValueEdgeSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardOrderSymmInr

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NChainChar

theorem edge_sum_typeFrame {K : Type} [Field K] (κ τ s N r p : ℕ) (hr : r ≤ N) (hrk : r = κ + (s + 1))
    (e : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) 0 ≃ Fin N) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) (ϖ : Kˣ)
    (q : GL (GlobalTheory.StepData.XIx (Fin κ) (Fin τ) 0 ⊕ Fin (s + 1)) K) (hq : GlobalTheory.RootEx.InN p q) :
    (∑ i : Fin r, ∑ j : Fin r, if GlobalTheory.chainEdge κ i j then
      (((GlobalTheory.StepData.typeFrame ϖ (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _))).bas⁻¹).val * q.val *
        (GlobalTheory.StepData.typeFrame ϖ (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _))).bas.val)
        (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr i)))
        (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr j))) else 0) =
      (ϖ : K) * GlobalTheory.RootEx.simpleSum q := by
  subst hrk
  rw [GlobalTheory.SymChain.NonZeroAt.typeFrame_bas_inv_val, GlobalTheory.SymChain.NonZeroAt.typeFrame_bas_val]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  let ε : Fin κ ⊕ Fin (s + 1) ≃ Fin (κ + (s + 1)) := finSumFinEquiv
  have hε : ∀ a, e.symm (Fin.castLE hr (ε a)) = Sum.inl a := by
    intro a
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    rw [he]
    rcases a with a | a <;> simp [ε, GlobalTheory.SymBridge.zPos]
  rw [← ε.sum_comp]
  simp only [← ε.sum_comp (fun j => ite _ _ _), hε]
  have h1 : ∀ i : Fin κ, GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (Sum.inl (Sum.inl i)) =
      Sum.inl (Sum.inl (Sum.inl i)) := fun i => rfl
  have h2 : ∀ i : Fin (s + 1), GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (Sum.inl (Sum.inr i)) =
      Sum.inr i := fun i => GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) i
  have hX : ∀ a b : GlobalTheory.StepData.XIx (Fin κ) (Fin τ) 0,
      q.val (Sum.inl a) (Sum.inl b) = (1 : Matrix (GlobalTheory.StepData.XIx (Fin κ) (Fin τ) 0 ⊕ Fin (s + 1)) _ K) (Sum.inl a) (Sum.inl b) :=
    fun a b => hq _ _ le_rfl
  have eε1 : ∀ i : Fin κ, (ε (Sum.inl i)).val = i.val := fun i => rfl
  have eε2 : ∀ i : Fin (s + 1), (ε (Sum.inr i)).val = κ + i.val := fun i => rfl
  simp only [Fintype.sum_sum_type, h1, h2, Sum.elim_inl, Sum.elim_inr, one_mul, mul_one, GlobalTheory.chainEdge, eε1, eε2]
  have A : ∀ x : Fin κ, ((∑ x_1 : Fin κ,
            if (x_1 : ℕ) = x + 1 ∧ (x : ℕ) + 1 ≠ κ then q.val (Sum.inl (Sum.inl (Sum.inl x))) (Sum.inl (Sum.inl (Sum.inl x_1)))
            else 0) +
          ∑ x_1 : Fin (s + 1),
            if κ + (x_1 : ℕ) = x + 1 ∧ (x : ℕ) + 1 ≠ κ then q.val (Sum.inl (Sum.inl (Sum.inl x))) (Sum.inr x_1) * (ϖ : K) ^ ((x_1 : ℕ) + 1)
            else 0) = 0 := by
    intro x
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro x_1 _
      rw [if_neg]
      omega
    · intro x_1 _
      split_ifs with h
      · rw [hX, Matrix.one_apply_ne]
        intro e
        have : x = x_1 := by simpa using e
        subst this
        omega
      · rfl
  have B : ∀ x : Fin (s + 1), ((∑ x_1 : Fin κ,
            if (x_1 : ℕ) = κ + x + 1 ∧ κ + (x : ℕ) + 1 ≠ κ then
              ((ϖ : K) ^ ((x : ℕ) + 1))⁻¹ * q.val (Sum.inr x) (Sum.inl (Sum.inl (Sum.inl x_1)))
            else 0) +
          ∑ x_1 : Fin (s + 1),
            if κ + (x_1 : ℕ) = κ + x + 1 ∧ κ + (x : ℕ) + 1 ≠ κ then
              ((ϖ : K) ^ ((x : ℕ) + 1))⁻¹ * q.val (Sum.inr x) (Sum.inr x_1) * (ϖ : K) ^ ((x_1 : ℕ) + 1)
            else 0) = (ϖ : K) * ∑ x_1 : Fin (s + 1), if (x_1 : ℕ) = x + 1 then q.val (Sum.inr x) (Sum.inr x_1) else 0 := by
    intro x
    rw [Finset.sum_eq_zero, zero_add, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun x_1 _ => ?_
      by_cases h : (x_1 : ℕ) = x + 1
      · rw [if_pos ⟨by omega, by omega⟩, if_pos h, h]
        have hϖ : (ϖ : K) ≠ 0 := ϖ.ne_zero
        field_simp
        ring
      · rw [if_neg (by omega), if_neg h, mul_zero]
    · intro x_1 _
      rw [if_neg]
      have := x_1.2
      omega
  simp only [A, B, Finset.sum_const_zero, zero_add, ← Finset.mul_sum]
  rfl

theorem redFn_conj_eq_one {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {a e : AE D} {P : Finset (Pl D.host.E)}
    {PP Q : Pl D.host.E} (ha : IsIdemSum a P) (hPP : PP ∈ P) (he : Formalism.L2.NTheta.IsIdemAt e PP) {n : GA D V}
    (hn : SuppAt e V n) (t : GA D V) (hS : finE V (t⁻¹ * n * t) ∈ St β) (hQ : Q ∈ P) (hne : PP ≠ Q) :
    redFn β Q (finE V (t⁻¹ * n * t)) = 1 := by
  refine GlobalTheory.DiagLiftFix.redFn_eq_one_of_ne ha hPP he ?_ hS hQ hne
  intro i j
  have h2 : mt V t⁻¹ * mt V t = 1 := by
    show mt V (t⁻¹ * t) = 1
    rw [inv_mul_cancel]; rfl
  have e1 : mt V (t⁻¹ * n * t) - 1 = mt V t⁻¹ * (mt V n - 1) * mt V t := by
    show mt V t⁻¹ * mt V n * mt V t - 1 = _
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2]
  rw [e1]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  have := hn m l
  linear_combination (mt V t⁻¹ i m * mt V t l j) * this

end GlobalTheory.NChainChar
