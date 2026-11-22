import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CoefficientLeOperatorNorm
import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
import Formalism.LogSumExpBounds.IsoTransfer
import Formalism.NormUnitaryBounds.Statement
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearCoefficients
import Formalism.NormUnitaryBounds.DetPolynomialWeights.LtSuccOfMemWeightCompositions
import Formalism.NormUnitaryBounds.DetPolynomialWeights.NormUnitary
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
import Formalism.LatticeTheta.ThetaShiftInversion
import Formalism.HarderNarasimhan.ShiftInvariance

open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix

namespace Formalism.HermitianLatticeCounting.P

section Frob
open scoped Matrix.Norms.Frobenius

lemma norm_exp_sub_one_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (x : A) :
    ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have h1 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • x ^ n) (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x
  have h2 : HasSum (fun n : ℕ => ‖x‖ ^ n / (n.factorial : ℝ)) (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ‖x‖
  have h1' := (hasSum_nat_add_iff' 1).mpr h1
  have h2' := (hasSum_nat_add_iff' 1).mpr h2
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    div_one] at h1' h2'
  refine h1'.norm_le_of_bounded h2' (fun n => ?_)
  rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  gcongr
  exact norm_pow_le' x (Nat.succ_pos n)

end Frob

noncomputable def n2 {N : ℕ} (v : Fin N → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖ ^ 2)

end Formalism.HermitianLatticeCounting.P
