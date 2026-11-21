import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuLineNormEq
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuFrameExists

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped Matrix ComplexOrder

namespace MuWeightChartSmooth

section Calculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} {x : F}

theorem contDiffAt_det {m : Type*} [Fintype m] [DecidableEq m] {M : F → Matrix m m ℂ}
    (hM : ∀ i j, ContDiffAt ℝ n (fun w => M w i j) x) : ContDiffAt ℝ n (fun w => (M w).det) x := by
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hM _ _)

theorem contDiffAt_star {f : F → ℂ} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun w => star (f w)) x :=
  (Complex.conjCLE.contDiff.contDiffAt).comp x hf

theorem contDiffAt_zpow_of_ne {f : F → ℝ} (hf : ContDiffAt ℝ n f x) (h0 : f x ≠ 0) (m : ℤ) :
    ContDiffAt ℝ n (fun w => f w ^ m) x := by
  rcases m with m | m
  · simpa using hf.pow m
  · simp only [zpow_negSucc]
    exact (hf.pow (m + 1)).fun_inv (pow_ne_zero _ h0)

theorem contDiffAt_sandwich {m : Type*} [Fintype m] {A B : F → Matrix m m ℂ}
    (hA : ∀ i j, ContDiffAt ℝ n (fun w => A w i j) x) (hB : ∀ i j, ContDiffAt ℝ n (fun w => B w i j) x)
    (i j : m) : ContDiffAt ℝ n (fun w => ((A w)ᴴ * B w * A w) i j) x := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact ContDiffAt.sum fun k _ =>
    (ContDiffAt.sum fun l _ => (contDiffAt_star (hA l i)).mul (hB l k)).mul (hA k j)

end Calculus

end MuWeightChartSmooth

end GroundTheory.Heights₂.Heights.LowerBoundFree
