import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

namespace ReciprocityTheory.AnForm.M

open OnePoint

noncomputable section

section Alg

variable {e : ℕ} {X : Type*} [TopologicalSpace X]

theorem FinHolAtlas.HoloOn.mul' {A : FinHolAtlas e X} {U : Set X} {f g : X → ℂ}
    (hf : A.HoloOn U f) (hg : A.HoloOn U g) : A.HoloOn U (fun x => f x * g x) :=
  fun j => (hf j).mul (hg j)

end Alg

namespace CompatibleChartOperations

def shearLE : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![v 0 - v 1, v 1]
  invFun v := ![v 0 + v 1, v 1]
  map_add' u v := by ext i; fin_cases i <;> simp [add_sub_add_comm]
  map_smul' c v := by ext i; fin_cases i <;> simp [mul_sub]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp

def shearCLE : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) := shearLE.toContinuousLinearEquiv

theorem shearCLE_apply_zero (v : Fin 2 → ℂ) : shearCLE v 0 = v 0 - v 1 := rfl

open scoped Classical in
theorem projLineChart1_symm_ite (t : Fin 1 → ℂ) :
    projectiveLineChartAtInfinity.symm t = if t 0 = 0 then ∞ else (((t 0)⁻¹ : ℂ) : OnePoint ℂ) := rfl

open scoped Classical in
theorem fsPot_U_ite (a : OnePoint ℂ) :
    fsPot.U a = if a = ∞ then projectiveLineChartAtInfinity.source else projectiveLineChartAtZero.source := rfl

open scoped Classical in
theorem fsPot_φ_ite (a p : OnePoint ℂ) : fsPot.φ a p = if a = ∞ then (1 / 2) * Real.log (1 + ‖crd1 p‖ ^ 2)
    else (1 / 2) * Real.log (1 + ‖crd0 p‖ ^ 2) := rfl

end CompatibleChartOperations

end

end ReciprocityTheory.AnForm.M
