import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadLApply
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprEqZeroOfCardNe

set_option autoImplicit false

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm GlobalTheory.LocFub
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.LocFub.TopDens

theorem dens_smul {n : ℕ} (c : ℂ) (α : Alt n) : dens (c • α) = c * dens α := by
  simp [dens, mul_div_assoc]

theorem dens_add {n : ℕ} (α β : Alt n) : dens (α + β) = dens α + dens β := by
  simp [dens, add_div]

theorem dens_zero {n : ℕ} : dens (0 : Alt n) = 0 := by simp [dens]

end GlobalTheory.LocFub.TopDens
