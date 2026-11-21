import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def fsGk (k : Fin 2) : ℝ → ℝ := if k = 0 then fubiniStudyProfile else fubiniStudyProfileInv

@[simp] theorem fsGk_zero : fsGk 0 = fubiniStudyProfile := by
  simp [fsGk]
@[simp] theorem fsGk_one : fsGk 1 = fubiniStudyProfileInv := by
  simp [fsGk]

theorem ell_ge {t B : ℝ} (ht : 0 < t) (htB : t ≤ Real.exp (-B)) : B ≤ Real.log (1 / t) := by
  rw [one_div, Real.log_inv]
  have h := Real.log_le_log ht htB
  rw [Real.log_exp] at h
  linarith

theorem one_le_exp_one : (1 : ℝ) ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp 1
  linarith

theorem ell_big {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    Real.exp (Real.exp 1) ≤ Real.log (1 / t) := by
  exact ell_ge ht ht0

theorem ell_ge_e {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    Real.exp 1 ≤ Real.log (1 / t) := by
  exact le_trans (Real.exp_le_exp.mpr one_le_exp_one) (ell_big ht ht0)

theorem ell_pos {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    0 < Real.log (1 / t) := by
  exact lt_of_lt_of_le (Real.exp_pos 1) (ell_ge_e ht ht0)

theorem logell_big {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    Real.exp 1 ≤ Real.log (Real.log (1 / t)) := by
  calc Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := (Real.log_exp _).symm
    _ ≤ Real.log (Real.log (1 / t)) := Real.log_le_log (Real.exp_pos _) (ell_big ht ht0)

theorem logell_pos {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    0 < Real.log (Real.log (1 / t)) := by
  exact lt_of_lt_of_le (Real.exp_pos 1) (logell_big ht ht0)

theorem eps_pos {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    0 < epsT 1 t := by
  unfold epsT
  exact div_pos (mul_pos one_pos (logell_pos ht ht0)) (ell_pos ht ht0)

end

end ReciprocityTheory.AnForm.P
