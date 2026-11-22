import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub

noncomputable section

namespace GlobalTheory.LKTorus.Model

open Complex

def conjC : ℂ →ₐ[ℝ] ℂ := (Complex.conjAe : ℂ →ₐ[ℝ] ℂ)

theorem conjC_apply (z : ℂ) : conjC z = (starRingEnd ℂ) z := rfl

def u : (ℂ × ℂ)ˣ := ⟨(1, -1), (1, -1), by ext <;> simp, by ext <;> simp⟩

end GlobalTheory.LKTorus.Model
