import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower

namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates

section F
open Finset

def bb (k rS : ℕ) (i : ℕ) : ℕ := if i < rS then i else if i < rS + (k + 1) then rS else i - k
def cc (k rS : ℕ) (j : ℕ) : ℕ := if j < rS then j else if j < rS + (k + 1) then rS else j

lemma inner (k rS j : ℕ) (hj : j < rS + (k + 1) + rS) :
    ((range (rS + (k + 1) + rS)).filter (fun i => bb k rS i < bb k rS j)).card = cc k rS j := by
  have h : (range (rS + (k + 1) + rS)).filter (fun i => bb k rS i < bb k rS j) = range (cc k rS j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    simp only [bb, cc]
    constructor
    · rintro ⟨h1, h2⟩
      split_ifs at h2 ⊢ <;> omega
    · intro h1
      refine ⟨by split_ifs at h1 <;> omega, ?_⟩
      split_ifs at h1 ⊢ <;> omega
  rw [h, card_range]

lemma total (k rS : ℕ) : ∑ j ∈ range (rS + (k + 1) + rS), cc k rS j = rS * (2 * k + 1 + 2 * rS) := by
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have e1 : ∑ x ∈ range rS, cc k rS x = ∑ x ∈ range rS, x :=
    Finset.sum_congr rfl fun x hx => by simp [cc, mem_range.1 hx]
  have e2 : ∑ x ∈ range (k + 1), cc k rS (rS + x) = ∑ x ∈ range (k + 1), rS :=
    Finset.sum_congr rfl fun x hx => by
      have := mem_range.1 hx
      simp only [cc]
      split_ifs <;> omega
  have e3 : ∑ x ∈ range rS, cc k rS (rS + (k + 1) + x) = ∑ x ∈ range rS, (rS + (k + 1) + x) :=
    Finset.sum_congr rfl fun x _ => by
      simp only [cc]
      split_ifs <;> omega
  rw [e1, e2, e3, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, card_range, card_range,
    smul_eq_mul, smul_eq_mul]
  have hS := Finset.sum_range_id_mul_two rS
  rcases rS with _ | m
  · simp
  · simp only [Nat.add_sub_cancel] at hS
    nlinarith [hS]

lemma countFree (k rS r : ℕ) (hr : r = rS + (k + 1) + rS) :
    (univ.filter (fun ij : Fin r × Fin r => bb k rS ij.1.val < bb k rS ij.2.val)).card =
      rS * (2 * k + 1 + 2 * rS) := by
  subst hr
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have h : ∀ j : Fin (rS + (k + 1) + rS),
      ∑ i : Fin (rS + (k + 1) + rS), (if bb k rS i.val < bb k rS j.val then 1 else 0) = cc k rS j.val := by
    intro j
    have h1 := inner k rS j.val j.isLt
    rw [Finset.card_filter] at h1
    rw [Fin.sum_univ_eq_sum_range (fun i => if bb k rS i < bb k rS j.val then 1 else 0), h1]
  rw [Finset.sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun j => cc k rS j), total]

end F

end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates

namespace Formalism.HermitianLattices.CumulantEstimateDefs

end Formalism.HermitianLattices.CumulantEstimateDefs
