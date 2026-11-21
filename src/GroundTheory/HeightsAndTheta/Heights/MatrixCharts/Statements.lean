import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def splitCoord (n m : ℕ) (w : Fin (n + m) → ℂ) : (Fin n → ℂ) × (Fin m → ℂ) :=
  (fun j => w (Fin.castAdd m j), fun k => w (Fin.natAdd n k))

def hermPair {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v w : ι → ℂ) : ℝ :=
  (star v ⬝ᵥ ((A.map fun x : ℝ => (x : ℂ)) *ᵥ w)).re

def hermValue {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (w : ι → ℂ) : ℝ :=
  hermPair A w w

def metricLength {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) (w : ι → ℂ) : ℝ :=
  Real.sqrt (hermValue Y⁻¹ w)

def covolume {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) {k : ℕ}
    (v : Fin k → ι → ℂ) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of fun j l => hermPair Y⁻¹ (v j) (v l)))

def logDetGram {g rk : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (F : Matrix (Fin g) (Fin rk) ℂ) : ℝ :=
  Real.log (Fᴴ * (Y⁻¹).map (fun x : ℝ => (x : ℂ)) * F).det.re

def intVecC {g : ℕ} (a : Fin g → ℤ) : Fin g → ℂ := fun k => (a k : ℂ)

def periodLattice {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Set (Fin g → ℂ) :=
  {w | ∃ a n : Fin g → ℤ, w = intVecC a + τ *ᵥ intVecC n}

def unitPolydisc (n : ℕ) : Set (Fin n → ℂ) := {z | ∀ j, ‖z j‖ < 1}

def cuspCoord {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (j : Fin a) : ℂ := z (Fin.castLE h j)

def cuspTime {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (j : Fin a) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.log ‖cuspCoord h z j‖⁻¹

def puncturedChart {n a : ℕ} (h : a ≤ n) (U : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {z | z ∈ U ∧ ∀ j, cuspCoord h z j ≠ 0}

def chartRadius {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) : ℝ :=
  Real.exp 1 + ∑ j, Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹

def chartImag {n a g : ℕ} (h : a ≤ n) (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  (τ0 z).map Complex.im + ∑ j, cuspTime h z j • B j

structure PeriodChartData where

  n : ℕ

  m : ℕ

  g : ℕ

  a : ℕ

  rk : ℕ
  a_le : a ≤ n
  U : Set (Fin n → ℂ)
  isOpen_U : IsOpen U
  U_subset : U ⊆ unitPolydisc n
  τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ
  τ0_analytic : ∀ j k, AnalyticOnNhd ℂ (fun z => τ0 z j k) U
  τ0_symm : ∀ z ∈ U, (τ0 z)ᵀ = τ0 z
  B : Fin a → Matrix (Fin g) (Fin g) ℝ

  B_psd : ∀ j, (B j).PosSemidef
  c : ℝ
  c_pos : 0 < c
  Y_ge : ∀ z ∈ puncturedChart a_le U, (chartImag a_le τ0 B z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef
  V : Set (Fin m → ℂ)
  isOpen_V : IsOpen V
  f : (Fin n → ℂ) × (Fin m → ℂ) → Matrix (Fin g) (Fin rk) ℂ
  f_analytic : ∀ j k, AnalyticOnNhd ℂ (fun p => f p j k) (U ×ˢ V)
  f_rank : ∀ p ∈ U ×ˢ V, (f p).rank = rk
  K : Set ((Fin n → ℂ) × (Fin m → ℂ))
  isCompact_K : IsCompact K
  K_subset : K ⊆ U ×ˢ V

namespace PeriodChartData

variable (D : PeriodChartData)

def Ustar : Set (Fin D.n → ℂ) := puncturedChart D.a_le D.U

def Y (z : Fin D.n → ℂ) : Matrix (Fin D.g) (Fin D.g) ℝ := chartImag D.a_le D.τ0 D.B z

def u (p : (Fin D.n → ℂ) × (Fin D.m → ℂ)) : ℝ := logDetGram (D.Y p.1) (D.f p)

def period (z : Fin D.n → ℂ) (ℓ : Fin D.a → ℂ) : Matrix (Fin D.g) (Fin D.g) ℂ :=
  D.τ0 z + ∑ j, (ℓ j / (2 * Real.pi * Complex.I)) • (D.B j).map (fun x : ℝ => (x : ℂ))

end PeriodChartData

structure ToricBlock (D : PeriodChartData) where
  r : ℕ
  r_le : r ≤ D.g
  support : ∀ (j : Fin D.a) (k l : Fin D.g), (r ≤ k.val ∨ r ≤ l.val) → D.B j k l = 0
  pos : ((∑ j, D.B j).submatrix (Fin.castLE r_le) (Fin.castLE r_le)).PosDef

structure SiegelFamily (N g rk : ℕ) where
  W : Set (Fin N → ℂ)
  isOpen_kappaOpenNeighbourhood : IsOpen W
  τ : (Fin N → ℂ) → Matrix (Fin g) (Fin g) ℂ
  τ_analytic : ∀ j k, AnalyticOnNhd ℂ (fun x => τ x j k) W
  τ_symm : ∀ x ∈ W, (τ x)ᵀ = τ x
  im_posDef : ∀ x ∈ W, ((τ x).map Complex.im).PosDef
  f : (Fin N → ℂ) → Matrix (Fin g) (Fin rk) ℂ
  f_analytic : ∀ j k, AnalyticOnNhd ℂ (fun x => f x j k) W
  f_rank : ∀ x ∈ W, (f x).rank = rk

end

end GroundTheory.Heights₂.Heights
