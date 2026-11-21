import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

namespace GlobalTheory.Diag.PG

open Formalism.BasicNotions

def bx (x eps : ℝ) : ℝ := Real.exp (x ^ eps)

variable (D : D7)

def Top (τ : D.what₂.Tau) : Prop :=
  ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t

def uFirst (τ : D.what₂.Tau) : ℝ := (((D.hc τ).u ⟨0, by have := D.R.m_add_three_le_k; omega⟩ : ℚ) : ℝ)

def uLast (τ : D.what₂.Tau) : ℝ := (((D.hc τ).u ⟨D.R.k - 1, by have := D.R.m_add_three_le_k; omega⟩ : ℚ) : ℝ)

def vFirst (τ : D.what₂.Tau) : ℝ := (((D.hc τ).v ⟨0, by have := D.R.m_add_three_le_k; omega⟩ : ℚ) : ℝ)

def vLast (τ : D.what₂.Tau) : ℝ := (((D.hc τ).v ⟨D.R.k - 2, by have := D.R.m_add_three_le_k; omega⟩ : ℚ) : ℝ)

def bFirst (τ : D.what₂.Tau) : ℝ := (((D.hc τ).b ⟨0, by have := D.R.two_le_m; omega⟩ : ℚ) : ℝ)

def bLast (τ : D.what₂.Tau) : ℝ := (((D.hc τ).b ⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩ : ℚ) : ℝ)

structure RankNums (x eps CD m f k lrd Del : ℝ) : Prop where
  m_lo : x ^ ((1 : ℝ) / 4) ≤ m
  mf : m ^ 4 ≤ f
  fk : f ≤ k
  k_lo : x ^ (eps / 2) * (m ^ 5 * f * x ^ eps) ≤ k
  k_hi : k ≤ x ^ (5 : ℝ)
  lrd_lo : Real.log 2 ≤ lrd
  lrd_hi : lrd ≤ x ^ (eps / 2)
  Del_lo : (k * f * x ^ eps) ^ CD ≤ Del
  Del_hi : Real.log Del ≤ x ^ (eps / 2)

structure Glob (x eps CD Cg CT : ℝ) : Prop where
  nums : RankNums x eps CD D.R.m D.R.f D.R.k (Real.log D.host.rdE) (D.s.Del : ℝ)
  rd_lo : 2 ≤ D.host.rdE
  g_win : ∀ i, ((D.R.k : ℝ) * bx x eps) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ bx x eps ^ Cg
  T_win : ∀ u, bx x eps ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ ((D.mem u).A.T : ℝ) ∧
    ((D.mem u).A.T : ℝ) ≤ bx x eps ^ (CT * (D.R.m : ℝ))
  gap : ∀ τ (j : ℕ) (h : j + 1 < D.R.m), x ^ (eps / 100) * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * x ^ eps ≤
    (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ)
  cloud : ∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧
    (((D.hc τ).v i : ℚ) : ℝ) ≤ 4 * (D.R.k : ℝ) * (D.s.Del : ℝ)
  off : ∀ τ, ¬ Top D τ → 4 * (D.R.k : ℝ) * (D.s.Del : ℝ) ≤ uFirst D τ - vFirst D τ ∧
    uFirst D τ - vFirst D τ ≤ 8 * (D.R.k : ℝ) * (D.s.Del : ℝ) ∧ uLast D τ = vLast D τ - 1 / 2

structure Nodes (x eps : ℝ) : Prop where
  b_win : ∀ τ j, Real.sqrt (bx x eps) ≤ (((D.hc τ).b j : ℚ) : ℝ) ∧ (((D.hc τ).b j : ℚ) : ℝ) ≤ bx x eps ^ 2
  bm : ∀ τ, bLast D τ ≤ 2 * bFirst D τ
  top : ∀ τ, Top D τ → Real.sqrt (bx x eps) ≤ uFirst D τ ∧ uFirst D τ ≤ bx x eps ^ 2 ∧
    3 ≤ bFirst D τ + uLast D τ ∧ bFirst D τ / 2 ≤ -uLast D τ

def SplitLab {R : Ranks} (H : Host R) (x eps : ℝ) : Prop :=
  (∃ J : ℝ, 1 ≤ J ∧ ⌊x ^ (eps / J / 5)⌋₊ ≤ H.splitBound) ∧ (R.o : ℝ) ≤ x ^ (eps / 100) ∧
    (H.QS : ℝ) ≤ 4 * R.n * x ^ (eps / 100)

structure Labels (x eps CG : ℝ) : Prop where
  secondLabelsNonempty : D.host.T2.Nonempty
  j0 : ∃ j0 : ℕ, Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ j0 ∧ 10 * j0 + 20 ≤ D.host.Lw
  split : SplitLab D.host x eps
  CG_pos : 0 < CG
  Gam : ∀ u, Real.log (D.mem u).A.GamP = CG * (D.R.m : ℝ) ^ 5 * D.R.f * x ^ eps

end GlobalTheory.Diag.PG

end
