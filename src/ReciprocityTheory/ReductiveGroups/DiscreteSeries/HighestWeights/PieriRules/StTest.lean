import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem pieriSt_isKHWVec_iff {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (μ : Fin n → ℝ) (v : W) :
    IsKHWVec ε E μ v ↔ Formalism.REAL.KHighest ε E μ v := Iff.rfl

theorem pieriSt_kRel_stdM {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.KRel ε (stdM n) := by
  intro a b c d _ _
  simp only [stdM]
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1 h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
  · simp [Matrix.single_mul_single_of_ne, h1, h2]

theorem pieriSt_stdM_diag {n : ℕ} (a : Fin n) :
    stdM n a a = Matrix.diagonal fun i => ((stdWt n i a : ℝ) : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hai : a = i
    · subst hai; simp [stdM, stdWt]
    · simp [stdM, stdWt, hai, Pi.single_apply]
  · simp [stdM, Matrix.single_apply, hij]
    intro h1 h2; exact hij (h1.symm.trans h2)

end ReciprocityTheory.ChartRestriction.DS.HW
