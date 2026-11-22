import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutPMulCutP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFunctionTwistBounded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedCapelliDeterminantSubleadingCoeffTrace

noncomputable section

open Matrix GlobalTheory.TorFin Formalism.REAL

namespace GlobalTheory.CentreFin

section Alg
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem qdet_mem {k : ℕ} {E : Fin k → Fin k → A} {S : Subalgebra ℂ A} (h : ∀ a b, E a b ∈ S) (u : ℂ) : qdet E u ∈ S := by
  unfold qdet qminor
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Subalgebra.add_mem _ ?_ (h _ _)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

theorem commute_qdet {k : ℕ} {E : Fin k → Fin k → A} {x : A} (h : ∀ a b, Commute x (E a b)) (u : ℂ) :
    Commute x (qdet E u) :=
  ((Subalgebra.mem_centralizer_iff ℂ).1 (qdet_mem (S := Subalgebra.centralizer ℂ {x})
    (fun a b => (Subalgebra.mem_centralizer_iff ℂ).2 fun _ hg => by rw [hg]; exact h a b) u) x rfl)

theorem exists_coef {k : ℕ} (E : Fin k → Fin k → A) (s : ℂ) {B : Subalgebra ℂ A} (hB : ∀ u, qdet E u ∈ B) :
    ∃ c : ℕ → A, c k = 1 ∧ (∀ j ≤ k, c j ∈ B) ∧ (∀ u, qdet E (u - s) = ∑ j ∈ Finset.range (k + 1), u ^ j • c j) ∧
      (∑ i, E i i = 0 ∨ ∃ j ≤ k, ∃ t : ℂ, ∑ i, E i i = c j + t • (1 : A)) := by
  cases k with
  | zero => exact ⟨fun _ => 1, rfl, fun _ _ => one_mem _, fun u => by simp [qdet, qminor], Or.inl (by simp)⟩
  | succ m =>
    obtain ⟨c, t, h1, h2, h3⟩ := _root_.GlobalTheory.CapelliNext.qdet_shift_next_coeff A m E s
    refine ⟨c, h1, fun j hj => ?_, h3, Or.inr ⟨m, m.le_succ, -t, by rw [h2, neg_smul, add_neg_cancel_right]⟩⟩
    exact GlobalTheory.coeff_mem_of_poly_values_mem A (Subalgebra.toSubmodule B) _ c (fun u => h3 u ▸ hB _) j (Nat.lt_succ_of_le hj)

end Alg

end GlobalTheory.CentreFin

end
