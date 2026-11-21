import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub

noncomputable section

namespace GlobalTheory.LKTorus.Model

open Complex

def conjC : ℂ →ₐ[ℝ] ℂ := (Complex.conjAe : ℂ →ₐ[ℝ] ℂ)

def conjCC : (ℂ × ℂ) →ₐ[ℝ] (ℂ × ℂ) := AlgHom.prodMap conjC conjC

theorem conjC_apply (z : ℂ) : conjC z = (starRingEnd ℂ) z := rfl

theorem conjCC_apply (z : ℂ × ℂ) : conjCC z = ((starRingEnd ℂ) z.1, (starRingEnd ℂ) z.2) := rfl

def u : (ℂ × ℂ)ˣ := ⟨(1, -1), (1, -1), by ext <;> simp, by ext <;> simp⟩

end GlobalTheory.LKTorus.Model
