import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantDominance

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem sum_fin_filter_lt_eq_range {N : ℕ} (G : ℕ → ℕ) (k : ℕ) :
    ∑ a : Fin N with a.val < k, G a.val = ∑ i ∈ Finset.range (min N k), G i := by
  rw [Finset.sum_filter]
  refine (Fin.sum_univ_eq_sum_range (fun i => if i < k then G i else 0) N).trans ?_
  show ∑ i ∈ Finset.range N, (if i < k then G i else 0) = _
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem rowNu_partial_sum {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r) (k : ℕ) :
    (∑ a : Fin r with a.val < k, rowNu (r := r) ν a) = ∑ t : Fin n with t.val < k, ν t := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ, G = fun i => if h : i < n then ν ⟨i, h⟩ else 0 := ⟨_, rfl⟩
  have h1 : (∑ a : Fin r with a.val < k, rowNu (r := r) ν a) =
      ∑ a : Fin r with a.val < k, G a.val :=
    Finset.sum_congr rfl fun a _ => by subst hG; rfl
  have h2 : (∑ t : Fin n with t.val < k, ν t) = ∑ t : Fin n with t.val < k, G t.val :=
    Finset.sum_congr rfl fun t _ => by subst hG; simp [t.isLt]
  rw [h1, h2, sum_fin_filter_lt_eq_range, sum_fin_filter_lt_eq_range]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hi'
    simp only [Finset.mem_range] at hi hi'
    have hin : ¬ i < n := by omega
    rw [hG]
    simp [hin]

end Formalism.GradedWeylDivisibility
