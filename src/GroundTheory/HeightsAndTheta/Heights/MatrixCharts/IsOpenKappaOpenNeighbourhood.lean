import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart

open Matrix

noncomputable section

def imPart {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  M.map Complex.im

def cplx {ι κ : Type*} (M : Matrix ι κ ℝ) : Matrix ι κ ℂ :=
  M.map (fun x : ℝ => (x : ℂ))

def qf {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (w : ι → ℂ) : ℝ :=
  (star w ⬝ᵥ (cplx Q *ᵥ w)).re

def punctured {n a : ℕ} (ha : a ≤ n) (U : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {z | z ∈ U ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}

def lwP₂ (z : ℂ) : ℝ :=
  Real.log (1 / ‖z‖) / (2 * Real.pi)

def chartY {n a g : ℕ} (ha : a ≤ n) (tau0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  imPart (tau0 z) + ∑ i : Fin a, lwP₂ (z (Fin.castLE ha i)) • B i

def chartR {n a : ℕ} (ha : a ≤ n) (z : Fin n → ℂ) : ℝ :=
  Real.exp 1 + ∑ i : Fin a, Real.log (1 / ‖z (Fin.castLE ha i)‖ ^ 2)

def gramLogDet {g k : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (F : Matrix (Fin g) (Fin k) ℂ) : ℝ :=
  Real.log (Fᴴ * cplx Y⁻¹ * F).det.re

structure PeriodChartData (n a g m k : ℕ) where
  U : Set (Fin n → ℂ)
  isOpen_U : IsOpen U
  U_sub : U ⊆ Metric.ball 0 1
  a_le : a ≤ n
  tau0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ
  tau_analyticOn : ∀ j l : Fin g, AnalyticOnNhd ℂ (fun z => tau0 z j l) U
  tau_transpose_eq : ∀ z ∈ U, (tau0 z)ᵀ = tau0 z
  B : Fin a → Matrix (Fin g) (Fin g) ℝ
  B_psd : ∀ i, (B i).PosSemidef
  c : ℝ
  c_pos : 0 < c
  Y_ge : ∀ z ∈ punctured a_le U, (chartY a_le tau0 B z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef
  V : Set (Fin m → ℂ)
  isOpen_V : IsOpen V
  f : (Fin n → ℂ) × (Fin m → ℂ) → Matrix (Fin g) (Fin k) ℂ
  f_analytic : ∀ (j : Fin g) (l : Fin k), AnalyticOnNhd ℂ (fun p => f p j l) (U ×ˢ V)
  f_rank : ∀ p ∈ U ×ˢ V, (f p).rank = k
  K : Set ((Fin n → ℂ) × (Fin m → ℂ))
  K_compact : IsCompact K
  K_sub : K ⊆ U ×ˢ V

namespace PeriodChartData

variable {n a g m k : ℕ} (D : PeriodChartData n a g m k)

def Y (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ := chartY D.a_le D.tau0 D.B z

def r (z : Fin n → ℂ) : ℝ := chartR D.a_le z

def u (p : (Fin n → ℂ) × (Fin m → ℂ)) : ℝ := gramLogDet (D.Y p.1) (D.f p)

def tau (l : Fin a → ℂ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  D.tau0 z + ∑ i : Fin a, (l i / (2 * (Real.pi : ℂ) * Complex.I)) • cplx (D.B i)

end PeriodChartData

def splitPt {n m : ℕ} (x : Fin (n + m) → ℂ) : (Fin n → ℂ) × (Fin m → ℂ) :=
  (fun i => x (Fin.castAdd m i), fun j => x (Fin.natAdd n j))

structure PshData (N g k : ℕ) where
  W : Set (Fin N → ℂ)
  isOpen_kappaOpenNeighbourhood : IsOpen W
  tau : (Fin N → ℂ) → Matrix (Fin g) (Fin g) ℂ
  tau_analytic : ∀ j l : Fin g, AnalyticOnNhd ℂ (fun z => tau z j l) W
  tau_symm : ∀ z ∈ W, (tau z)ᵀ = tau z
  im_posDef : ∀ z ∈ W, (imPart (tau z)).PosDef
  F : (Fin N → ℂ) → Matrix (Fin g) (Fin k) ℂ
  F_analytic : ∀ (j : Fin g) (l : Fin k), AnalyticOnNhd ℂ (fun z => F z j l) W
  F_rank : ∀ z ∈ W, (F z).rank = k

structure ToricBlock {n a g m k : ℕ} (D : PeriodChartData n a g m k) (r : ℕ) : Prop where
  r_le : r ≤ g
  B_support : ∀ (i : Fin a) (j l : Fin g), (r ≤ j.val ∨ r ≤ l.val) → D.B i j l = 0
  sum_posDef : ((∑ i, D.B i).submatrix (Fin.castLE r_le) (Fin.castLE r_le)).PosDef

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
