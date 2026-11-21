import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtPrim

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

def wZ (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 - I * fderiv ℝ f ζ I)

def wZb (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 + I * fderiv ℝ f ζ I)

def Hh (TT : ℝ) : Set ℂ := {w | TT < Complex.normSq (Complex.exp w)}

theorem normSq_exp (w : ℂ) : Complex.normSq (Complex.exp w) = Real.exp w.re ^ 2 := by

  first
    | rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    | simp [Complex.normSq_eq_norm_sq, Complex.norm_exp]

theorem isOpen_Hh (TT : ℝ) : IsOpen (Hh TT) := isOpen_lt continuous_const (Complex.continuous_normSq.comp Complex.continuous_exp)

theorem convex_Hh (TT : ℝ) : Convex ℝ (Hh TT) := by

  intro w1 h1 w2 h2 a b ha hb hab
  simp only [Hh, Set.mem_setOf_eq, normSq_exp] at h1 h2 ⊢
  have hre : (a • w1 + b • w2).re = a * w1.re + b * w2.re := by simp
  rw [hre]
  rcases le_total w1.re w2.re with h | h
  · calc TT < Real.exp w1.re ^ 2 := h1
      _ ≤ Real.exp (a * w1.re + b * w2.re) ^ 2 := by
        have e : a * w1.re + b * w2.re - w1.re = b * (w2.re - w1.re) := by
          rw [show a = 1 - b by linarith]; ring
        have : w1.re ≤ a * w1.re + b * w2.re := by nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
        gcongr
  · calc TT < Real.exp w2.re ^ 2 := h2
      _ ≤ Real.exp (a * w1.re + b * w2.re) ^ 2 := by
        have e : a * w1.re + b * w2.re - w2.re = a * (w1.re - w2.re) := by
          rw [show b = 1 - a by linarith]; ring
        have : w2.re ≤ a * w1.re + b * w2.re := by nlinarith [mul_nonneg ha (sub_nonneg.2 h)]
        gcongr

def bet (α : ℂ → ℂ) (w : ℂ) : ℂ := α (Complex.exp w) * Complex.exp w

def omL : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (2 : ℝ) • (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp (ContinuousLinearMap.mul ℝ ℂ)

theorem omL_apply (c v : ℂ) : omL c v = 2 * (c * v).im := by

  simp [omL]

def om (α : ℂ → ℂ) (w : ℂ) : ℂ →L[ℝ] ℝ := omL (bet α w)

theorem om_apply (α : ℂ → ℂ) (w v : ℂ) : om α w v = 2 * (bet α w * v).im := omL_apply _ _

theorem bet_periodic (α : ℂ → ℂ) (w : ℂ) (k : ℤ) : bet α (w + (k : ℂ) * (2 * Real.pi * I)) = bet α w := by

  simp only [bet, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
