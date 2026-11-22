import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.IsOpenKappaOpenNeighbourhood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart

open Matrix

noncomputable section

theorem unitPolydisc_eq_ball (n : ℕ) :
    GroundTheory.Heights₂.Heights.unitPolydisc n = Metric.ball (0 : Fin n → ℂ) 1 := by
  ext z
  simp [GroundTheory.Heights₂.Heights.unitPolydisc, Metric.mem_ball, dist_zero_right,
    pi_norm_lt_iff one_pos]

theorem cuspTime_eq_logWeight {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (j : Fin a) :
    GroundTheory.Heights₂.Heights.cuspTime h z j = lwP₂ (z (Fin.castLE h j)) := by
  simp only [GroundTheory.Heights₂.Heights.cuspTime, GroundTheory.Heights₂.Heights.cuspCoord, lwP₂, one_div]
  ring

theorem chartImag_eq_chartY {n a g : ℕ} (h : a ≤ n)
    (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (z : Fin n → ℂ) : GroundTheory.Heights₂.Heights.chartImag h τ0 B z = chartY h τ0 B z := by
  simp only [GroundTheory.Heights₂.Heights.chartImag, chartY, imPart, cuspTime_eq_logWeight]

namespace PeriodChartData

def ofBundled (D : GroundTheory.Heights₂.Heights.PeriodChartData) :
    PeriodChartData D.n D.a D.g D.m D.rk where
  U := D.U
  isOpen_U := D.isOpen_U
  U_sub := by rw [← unitPolydisc_eq_ball]; exact D.U_subset
  a_le := D.a_le
  tau0 := D.τ0
  tau_analyticOn := D.τ0_analytic
  tau_transpose_eq := D.τ0_symm
  B := D.B
  B_psd := D.B_psd
  c := D.c
  c_pos := D.c_pos
  Y_ge := fun z hz => by rw [← chartImag_eq_chartY]; exact D.Y_ge z hz
  V := D.V
  isOpen_V := D.isOpen_V
  f := D.f
  f_analytic := D.f_analytic
  f_rank := D.f_rank
  K := D.K
  K_compact := D.isCompact_K
  K_sub := D.K_subset

def bundle {n a g m k : ℕ} (D : PeriodChartData n a g m k) :
    GroundTheory.Heights₂.Heights.PeriodChartData where
  n := n
  m := m
  g := g
  a := a
  rk := k
  a_le := D.a_le
  U := D.U
  isOpen_U := D.isOpen_U
  U_subset := by rw [unitPolydisc_eq_ball]; exact D.U_sub
  τ0 := D.tau0
  τ0_analytic := D.tau_analyticOn
  τ0_symm := D.tau_transpose_eq
  B := D.B
  B_psd := D.B_psd
  c := D.c
  c_pos := D.c_pos
  Y_ge := fun z hz => by rw [chartImag_eq_chartY]; exact D.Y_ge z hz
  V := D.V
  isOpen_V := D.isOpen_V
  f := D.f
  f_analytic := D.f_analytic
  f_rank := D.f_rank
  K := D.K
  isCompact_K := D.K_compact
  K_subset := D.K_sub

section ofBundled

variable (D : GroundTheory.Heights₂.Heights.PeriodChartData)

@[simp] theorem ofBundled_U : (ofBundled D).U = D.U := rfl
@[simp] theorem periodChartData_ofBundled_tau : (ofBundled D).tau0 = D.τ0 := rfl
@[simp] theorem ofBundled_B : (ofBundled D).B = D.B := rfl
@[simp] theorem ofBundled_c : (ofBundled D).c = D.c := rfl
@[simp] theorem ofBundled_V : (ofBundled D).V = D.V := rfl
@[simp] theorem ofBundled_f : (ofBundled D).f = D.f := rfl
@[simp] theorem ofBundled_K : (ofBundled D).K = D.K := rfl

end ofBundled

section bundle

variable {n a g m k : ℕ} (D : PeriodChartData n a g m k)

@[simp] theorem bundle_n : D.bundle.n = n := rfl
@[simp] theorem bundle_a : D.bundle.a = a := rfl
@[simp] theorem bundle_g : D.bundle.g = g := rfl
@[simp] theorem bundle_m : D.bundle.m = m := rfl
@[simp] theorem bundle_rk : D.bundle.rk = k := rfl
end bundle

end PeriodChartData

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
