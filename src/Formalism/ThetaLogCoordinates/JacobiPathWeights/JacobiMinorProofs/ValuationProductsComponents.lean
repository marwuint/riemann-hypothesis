import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementA
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementE
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ActFormContract
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.PathProductHighestWeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ExistsSuppOfEvalNe

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace A0

def trInv {R : Type*} [CommRing R] {n : ℕ} (m : (Matrix (Fin n) (Fin n) R)ˣ) : (Matrix (Fin n) (Fin n) R)ˣ :=
  ⟨(↑m⁻¹ : Matrix _ _ R).transpose, (↑m : Matrix _ _ R).transpose,
    by rw [← Matrix.transpose_mul]; simp, by rw [← Matrix.transpose_mul]; simp⟩

theorem trInv_val {R : Type*} [CommRing R] {n : ℕ} (m : (Matrix (Fin n) (Fin n) R)ˣ) :
    (↑(trInv m) : Matrix (Fin n) (Fin n) R) = (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose := rfl

end A0

namespace A0

theorem trunc (R : Type*) [CommRing R] (n i : ℕ) (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ) (N : ℕ)
    (hN : i ≤ N) : ∀ I : Finset (Fin n),
    ∃ Q : Finset (Fin n) → MvPolynomial (ℕ × Fin n) R,
      (∀ I', Q I' ∈ supported R {x : ℕ × Fin n | i ≤ x.1}) ∧
      pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) R)) N I =
        ∑ I' : Finset (Fin n),
          pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) R)) i I' * Q I' := by
  induction N, hN using Nat.le_induction with
  | base =>
    intro I
    refine ⟨fun I' => if I' = I then 1 else 0, fun I' => ?_, ?_⟩
    · dsimp only
      split
      · exact one_mem _
      · exact zero_mem _
    · simp
  | succ N hN ih =>
    intro I
    by_cases hch : colHeight (μ (N + 1)) c = colHeight (μ N) c
    · rw [pathWord, if_pos hch]
      exact ih I
    · rw [pathWord, if_neg hch]
      choose Q hQ1 hQ2 using ih
      have hX : ∀ m : Fin n, (X (N, m) : MvPolynomial (ℕ × Fin n) R) ∈
          supported R {x : ℕ × Fin n | i ≤ x.1} := fun m => by
        rw [supported_eq_adjoin_X]
        exact Algebra.subset_adjoin ⟨(N, m), hN, rfl⟩
      unfold stepF
      split
      · refine ⟨fun I' => ∑ m ∈ I, ((sg I m : ℤ) : MvPolynomial (ℕ × Fin n) R) * Q (I.erase m) I' * X (N, m),
          fun I' => ?_, ?_⟩
        · exact sum_mem fun m _ => mul_mem (mul_mem (intCast_mem _ _) (hQ1 _ _)) (hX m)
        · unfold wedgeF
          simp only [hQ2, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => ?_
          ring
      · refine ⟨fun I' => ∑ m ∈ Iᶜ, ((sg I m : ℤ) : MvPolynomial (ℕ × Fin n) R) * X (N, m) * Q (insert m I) I',
          fun I' => ?_, ?_⟩
        · exact sum_mem fun m _ => mul_mem (mul_mem (intCast_mem _ _) (hX m)) (hQ1 _ _)
        · unfold contrF
          simp only [hQ2, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => ?_
          ring

end A0

namespace A0

theorem pathWord_card {R : Type*} [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) (c : ℤ) (Xr : ℕ → Fin n → R) :
    ∀ j ≤ N, ∀ J : Finset (Fin n), pathWord isVec μ c Xr j J ≠ 0 →
      J.card = if 1 ≤ c then colHeight (μ j) c else n - colHeight (μ j) c := by
  intro j
  induction j with
  | zero =>
    intro _ J hJ
    have h0 : J = ∅ := by
      by_contra hne
      exact hJ (if_neg hne)
    rw [h0, hp.1, Paths.colHeight_zero]
    split_ifs <;> simp
  | succ j ih =>
    intro hj J hJ
    have ih' := ih (by omega)
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, if_pos hch] at hJ
      rw [hch]
      exact ih' J hJ
    · rw [pathWord, if_neg hch] at hJ
      have hh := Paths.path_height hp (show j < N by omega) c
      have hle := Paths.colHeight_le (μ j) c
      have hle' := Paths.colHeight_le (μ (j + 1)) c
      unfold stepF at hJ
      cases hup : (isVec j == decide (1 ≤ c))
      · rw [hup] at hJ
        simp only [Bool.false_eq_true, if_false] at hJ
        unfold contrF at hJ
        obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hJ
        have e := ih' _ (right_ne_zero_of_mul hne)
        rw [Finset.card_insert_of_notMem (Finset.mem_compl.1 hm)] at e
        by_cases h1 : 1 ≤ c
        · have hv : isVec j = false := by simpa [h1] using hup
          rw [hv] at hh
          simp only [Bool.false_eq_true, if_false] at hh
          rw [if_pos h1] at e ⊢
          omega
        · have hv : isVec j = true := by simpa [h1] using hup
          rw [hv] at hh
          simp only [if_true] at hh
          rw [if_neg h1] at e ⊢
          omega
      · rw [hup] at hJ
        simp only [if_true] at hJ
        unfold wedgeF at hJ
        obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hJ
        have e := ih' _ (right_ne_zero_of_mul (left_ne_zero_of_mul hne))
        have hpos : 0 < J.card := Finset.card_pos.2 ⟨m, hm⟩
        rw [Finset.card_erase_of_mem hm] at e
        by_cases h1 : 1 ≤ c
        · have hv : isVec j = true := by simpa [h1] using hup
          rw [hv] at hh
          simp only [if_true] at hh
          rw [if_pos h1] at e ⊢
          omega
        · have hv : isVec j = false := by simpa [h1] using hup
          rw [hv] at hh
          simp only [Bool.false_eq_true, if_false] at hh
          rw [if_neg h1] at e ⊢
          omega

section Gen

variable (k : Type) [Field k] {n : ℕ} (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]

def gam (n : ℕ) (τ : Type) : (Matrix (Fin n) (Fin n) (MvPolynomial τ (GenField k n)))ˣ :=
  ⟨(genMat k n)⁻¹.map C, (genMat k n).map C,
    by rw [← Matrix.map_mul, genMat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)],
    by rw [← Matrix.map_mul, genMat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]⟩

theorem gam_val (n : ℕ) (τ : Type) :
    (↑(gam k n τ) : Matrix (Fin n) (Fin n) (MvPolynomial τ (GenField k n))) = (genMat k n)⁻¹.map C := rfl

variable {k isVec S}

end Gen

end A0

namespace A0

section Jacobi

variable {R : Type} [CommRing R] {n : ℕ}

def eps (I : Finset (Fin n)) : ℤ := ∏ a ∈ I, (-1) ^ (a.val + n + 1)

end Jacobi

end A0

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
