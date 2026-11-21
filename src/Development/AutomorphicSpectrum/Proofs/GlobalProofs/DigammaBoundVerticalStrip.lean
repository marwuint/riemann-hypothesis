import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionStrip
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthGamma
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.DigammaStrip

theorem norm_sin_le_exp (u : ℂ) : ‖Complex.sin u‖ ≤ Real.exp |u.im| := by
  have h1 : ‖Complex.exp (-u * I)‖ ≤ Real.exp |u.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by simpa using le_abs_self u.im)
  have h2 : ‖Complex.exp (u * I)‖ ≤ Real.exp |u.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by simpa using neg_le_abs u.im)
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h3 := norm_sub_le (Complex.exp (-u * I)) (Complex.exp (u * I))
  simp only [Complex.norm_ofNat]
  linarith

end GlobalTheory.CompanionTheory.DigammaStrip
