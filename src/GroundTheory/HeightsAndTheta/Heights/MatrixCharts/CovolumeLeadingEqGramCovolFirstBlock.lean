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

theorem puncturedChart_eq_punctured {n a : ℕ} (h : a ≤ n) (U : Set (Fin n → ℂ)) :
    GroundTheory.Heights₂.Heights.puncturedChart h U = punctured h U := rfl

theorem chartImag_eq_chartY {n a g : ℕ} (h : a ≤ n)
    (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (z : Fin n → ℂ) : GroundTheory.Heights₂.Heights.chartImag h τ0 B z = chartY h τ0 B z := by
  simp only [GroundTheory.Heights₂.Heights.chartImag, chartY, imPart, cuspTime_eq_logWeight]

theorem hermPair_inv_eq_realIP {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (v w : Fin g → ℂ) :
    GroundTheory.Heights₂.Heights.hermPair Y⁻¹ v w = realIP Y v w := rfl

theorem hermValue_eq_qf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (w : ι → ℂ) :
    GroundTheory.Heights₂.Heights.hermValue A w = qf A w := rfl

theorem metricLength_eq_yNorm {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℂ) :
    GroundTheory.Heights₂.Heights.metricLength Y w = yNorm Y w := rfl

theorem logDetGram_eq_gramLogDet {g k : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ)
    (F : Matrix (Fin g) (Fin k) ℂ) : GroundTheory.Heights₂.Heights.logDetGram Y F = gramLogDet Y F := rfl

theorem splitCoord_eq_splitPt (n m : ℕ) : GroundTheory.Heights₂.Heights.splitCoord n m = splitPt := rfl

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

theorem Ustar_ofBundled : (ofBundled D).Ustar = D.Ustar := rfl

theorem tau_ofBundled (ℓ : Fin D.a → ℂ) (z : Fin D.n → ℂ) :
    (ofBundled D).tau ℓ z = D.period z ℓ := rfl

end ofBundled

section bundle

variable {n a g m k : ℕ} (D : PeriodChartData n a g m k)

@[simp] theorem bundle_n : D.bundle.n = n := rfl
@[simp] theorem bundle_a : D.bundle.a = a := rfl
@[simp] theorem bundle_g : D.bundle.g = g := rfl
@[simp] theorem bundle_m : D.bundle.m = m := rfl
@[simp] theorem bundle_rk : D.bundle.rk = k := rfl
theorem bundle_U : D.bundle.U = D.U := rfl
theorem bundle_τ0 : D.bundle.τ0 = D.tau0 := rfl
theorem bundle_B : D.bundle.B = D.B := rfl
theorem bundle_c : D.bundle.c = D.c := rfl
theorem bundle_V : D.bundle.V = D.V := rfl
theorem bundle_f : D.bundle.f = D.f := rfl
theorem bundle_K : D.bundle.K = D.K := rfl

theorem bundle_Ustar : D.bundle.Ustar = D.Ustar := rfl

theorem bundle_period (z : Fin n → ℂ) (ℓ : Fin a → ℂ) : D.bundle.period z ℓ = D.tau ℓ z := rfl

theorem ofBundled_bundle : ofBundled D.bundle = D := rfl

end bundle

end PeriodChartData

namespace ToricBlock

def toBundled {D : GroundTheory.Heights₂.Heights.PeriodChartData} {r : ℕ}
    (T : ToricBlock (PeriodChartData.ofBundled D) r) : GroundTheory.Heights₂.Heights.ToricBlock D where
  r := r
  r_le := T.r_le
  support := T.B_support
  pos := T.sum_posDef

theorem toBundled_r {D : GroundTheory.Heights₂.Heights.PeriodChartData} {r : ℕ}
    (T : ToricBlock (PeriodChartData.ofBundled D) r) : (toBundled T).r = r := rfl

end ToricBlock

namespace PshData

def ofSiegelFamily {N g k : ℕ} (S : GroundTheory.Heights₂.Heights.SiegelFamily N g k) : PshData N g k where
  W := S.W
  isOpen_kappaOpenNeighbourhood := S.isOpen_kappaOpenNeighbourhood
  tau := S.τ
  tau_analytic := S.τ_analytic
  tau_symm := S.τ_symm
  im_posDef := S.im_posDef
  F := S.f
  F_analytic := S.f_analytic
  F_rank := S.f_rank

theorem ofSiegelFamily_alt {N g k : ℕ} (S : GroundTheory.Heights₂.Heights.SiegelFamily N g k) :
    (ofSiegelFamily S).W = S.W := rfl
theorem ofSiegelFamily_tau {N g k : ℕ} (S : GroundTheory.Heights₂.Heights.SiegelFamily N g k) :
    (ofSiegelFamily S).tau = S.τ := rfl
theorem ofSiegelFamily_F {N g k : ℕ} (S : GroundTheory.Heights₂.Heights.SiegelFamily N g k) :
    (ofSiegelFamily S).F = S.f := rfl

theorem gramLogDet_ofSiegelFamily {N g k : ℕ} (S : GroundTheory.Heights₂.Heights.SiegelFamily N g k)
    (x : Fin N → ℂ) :
    gramLogDet (imPart ((ofSiegelFamily S).tau x)) ((ofSiegelFamily S).F x) =
      GroundTheory.Heights₂.Heights.logDetGram ((S.τ x).map Complex.im) (S.f x) := rfl

end PshData

def realIPForm {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (realIP Y)
    (fun v v' w => by simp [realIP, star_add, add_dotProduct])
    (fun c v w => by simp [realIP, star_smul, smul_dotProduct])
    (fun v w w' => by simp [realIP, mulVec_add, dotProduct_add])
    (fun c v w => by simp [realIP, mulVec_smul, dotProduct_smul])

theorem realIPForm_apply {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (v w : Fin g → ℂ) :
    realIPForm Y v w = realIP Y v w := rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
