import Mathlib

namespace Formalism.FourierDecayAlt.P.Herglotz

open Real Filter Topology Finset

variable {d : ℕ}

noncomputable def ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ))

lemma ee_eq (x : Fin d → ℝ) (σ : Fin d → ℤ) :
    ee x σ = Complex.exp (((2 * π * ∑ j, (σ j : ℝ) * x j : ℝ) : ℂ) * Complex.I) := by
  unfold ee
  congr 1
  push_cast
  ring

lemma norm_ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ‖ee x σ‖ = 1 := by
  rw [ee_eq]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ee_mul_conj (x : Fin d → ℝ) (σ σ' : Fin d → ℤ) :
    ee x σ * starRingEnd ℂ (ee x σ') = ee x (σ - σ') := by
  rw [ee_eq, ee_eq, ee_eq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  push_cast
  ring

end Formalism.FourierDecayAlt.P.Herglotz

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
