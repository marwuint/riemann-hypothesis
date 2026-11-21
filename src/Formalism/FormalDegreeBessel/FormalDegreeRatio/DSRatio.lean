import Formalism.FormalDegreeBessel.StatementDS
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds

open Finset Formalism.REAL

noncomputable section

namespace Formalism.QuantumDeterminants

private theorem fdegDen_ne_zero (n : ℕ) :
    (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro a _
  rw [Finset.prod_ne_zero_iff]
  intro b hb
  have hab : a < b := by simpa using hb
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

theorem formalDegreeShiftRatio_holds : FdegRatio := by
  intro n μ s hinj hint hinj'
  have hD := fdegDen_ne_zero n
  have hN : ∀ a b : Fin n, a < b → |μ a - μ b| ≠ 0 := fun a b h =>
    abs_ne_zero.mpr (sub_ne_zero.mpr (hinj.ne h.ne))
  have es : ((μ + Pi.single s 1 : Fin n → ℝ)) s = μ s + 1 := by simp
  have eo : ∀ t, t ≠ s → ((μ + Pi.single s 1 : Fin n → ℝ)) t = μ t := fun t ht => by simp [Pi.single_apply, ht]
  set h : Fin n → ℝ := fun t => (μ s + 1 - μ t) / (μ s - μ t) with hh
  have hsign : ∀ t, t ≠ s → |μ s + 1 - μ t| / |μ s - μ t| = h t := by
    intro t ht
    obtain ⟨m, hm⟩ := hint s t
    have h1 : μ s - μ t ≠ 0 := sub_ne_zero.mpr (hinj.ne ht.symm)
    have h2 : μ s + 1 - μ t ≠ 0 := by
      have := hinj'.ne ht.symm
      rw [es, eo t ht] at this
      exact sub_ne_zero.mpr this
    have e2 : μ s + 1 - μ t = (m : ℝ) + 1 := by linarith
    rw [hm] at h1
    rw [e2] at h2
    have hm0 : m ≠ 0 := by exact_mod_cast h1
    have hm1 : m + 1 ≠ 0 := by exact_mod_cast h2
    rw [← abs_div, abs_of_pos]
    rw [e2, hm]
    rcases lt_or_gt_of_ne hm0 with hneg | hpos
    · have hle : m ≤ -2 := by omega
      have : (m : ℝ) ≤ -2 := by exact_mod_cast hle
      apply div_pos_of_neg_of_neg <;> linarith
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hpos
      apply div_pos <;> linarith
  have hr : ∀ a b : Fin n, a < b → |((μ + Pi.single s 1 : Fin n → ℝ)) a - ((μ + Pi.single s 1 : Fin n → ℝ)) b| / |μ a - μ b| =
      (if a = s then h b else 1) * (if b = s then h a else 1) := by
    intro a b hab
    by_cases has : a = s
    · have hbs : b ≠ s := has ▸ hab.ne'
      rw [if_pos has, if_neg hbs, mul_one, has, es, eo b hbs]
      exact hsign b hbs
    · by_cases hbs : b = s
      · rw [if_neg has, if_pos hbs, one_mul, hbs, es, eo a has, abs_sub_comm (μ a), abs_sub_comm (μ a)]
        exact hsign a has
      · rw [if_neg has, if_neg hbs, mul_one, eo a has, eo b hbs]
        exact div_self (hN a b hab)
  unfold fdegHC
  rw [div_div_div_cancel_right₀ hD, ← Finset.prod_div_distrib]
  calc ∏ a : Fin n, (∏ b ∈ univ.filter (fun b : Fin n => a < b),
          |((μ + Pi.single s 1 : Fin n → ℝ)) a - ((μ + Pi.single s 1 : Fin n → ℝ)) b|) /
          ∏ b ∈ univ.filter (fun b : Fin n => a < b), |μ a - μ b|
      = ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          ((if a = s then h b else 1) * (if b = s then h a else 1)) := by
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [← Finset.prod_div_distrib]
        exact Finset.prod_congr rfl fun b hb => hr a b (by simpa using hb)
    _ = ∏ t : Fin n, ((if s < t then h t else 1) * (if t < s then h t else 1)) := by
        simp only [Finset.prod_mul_distrib]
        congr 1
        · rw [Finset.prod_eq_single s]
          · rw [Finset.prod_filter]
            exact Finset.prod_congr rfl fun t _ => by simp
          · intro a _ has
            exact Finset.prod_eq_one fun b _ => if_neg has
          · intro h'; exact absurd (Finset.mem_univ s) h'
        · refine Finset.prod_congr rfl fun a _ => ?_
          rw [Finset.prod_ite_eq']
          simp
    _ = ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') := by
        rw [← Finset.filter_ne' univ s, Finset.prod_filter]
        refine Finset.prod_congr rfl fun t _ => ?_
        rcases lt_trichotomy s t with hst | hst | hst
        · simp [hst, hst.ne', not_lt.mpr hst.le, hh]
        · subst hst; simp
        · simp [hst, hst.ne, not_lt.mpr hst.le, hh]

theorem capelliHighestWeight_holds : CapelliHW := by
  intro V _ _ n E ν v hG hHW Y
  rw [quantumDetHighestWeight_holds V n E ν v hG hHW]
  congr 1
  unfold capP
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [rhoStd]
  push_cast
  ring

end Formalism.QuantumDeterminants
