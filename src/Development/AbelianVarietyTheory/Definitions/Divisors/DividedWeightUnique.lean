import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.LocalRingCardinality.DataParams₂
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLimDeg

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField

noncomputable section

namespace GlobalTheory.MeanTop

structure Wts (ι : Type) (N : ℕ) where

  kc : ℕ

  p : ℕ

  T : ℕ

  Dd : ℕ

  c0 : ℤ

  h0 : ℤ

  S : ℝ

  eta : ℝ

  b : ℝ

  w : ι → ℝ

  u : ι → Fin N → ℤ

  u1 : ι → Fin N → ℤ

namespace Wts

variable {ι : Type} {N : ℕ} (W : Wts ι N)

def u' : ι → Fin N → ℤ := fun τ i => if (i : ℕ) < W.p then W.u1 τ i else W.u1 τ i + 3 * (N : ℤ)

def g : ℝ := (W.h0 : ℝ) / (4 * W.T)

def IsDiv : Prop :=
  ∀ τ, (∀ a : Fin N, (a : ℕ) + 1 = W.kc → W.u1 τ a = 0) ∧ ∀ a b : Fin N, (b : ℕ) = a + 1 →
    W.u1 τ a - W.u1 τ b =
      (W.u τ a - W.u τ b + if (b : ℕ) = W.p then -W.c0 - (2 * (N : ℤ) - 2) else 2) / ((W.T : ℤ) + W.Dd + 1)

structure Hyp : Prop where
  kc_pos : 1 ≤ W.kc
  kc_lt : W.kc < W.p
  p_lt : W.p < N
  small : N - W.p < W.p
  weightConst_nonneg : 0 ≤ W.c0
  anchor : ∀ τ (a : Fin N), (a : ℕ) + 1 = W.kc → W.u τ a = 0
  h1 : 4 * W.Dd + 4 ≤ W.T
  h2 : 4 * (W.c0 + 2 * N + W.T + W.Dd + 1) ≤ W.h0 ∧ 24 * (N : ℤ) * W.T ≤ W.h0
  h3node : ∀ τ (a : Fin N), W.kc ≤ (a : ℕ) → |(W.u τ a : ℝ) + W.w τ| ≤ W.eta + W.S + N
  h3cloud : ∀ τ (a : Fin N), (a : ℕ) < W.kc → 0 ≤ W.u τ a ∧ (W.u τ a : ℝ) ≤ W.S
  h3w : ∀ τ, 4 * ((W.eta + W.S + N) + W.S + W.c0 + 2 * N) + 20 * N * W.T ≤ W.w τ
  h4 : ∀ τ (a b : Fin N), (b : ℕ) = a + 1 →
    ((b : ℕ) ≠ W.p → ((W.T : ℤ) + W.Dd + 2) * ((W.T : ℤ) + W.Dd + 2 + 2 * N) ≤ W.u τ a - W.u τ b + 2) ∧
    (W.kc ≤ (a : ℕ) → W.h0 - 1 ≤ W.u τ a - W.u τ b) ∧ ((b : ℕ) = W.p → W.h0 ≤ W.u τ a - W.u τ b)
  h5 : ∀ τ a, |(W.u τ a : ℝ)| + W.c0 + 4 * N ≤ 2 * W.b

end Wts

def l1 {ι : Type} [Fintype ι] {N : ℕ} (v : ι → Fin N → ℤ) : ℝ := ∑ τ, ∑ i, |(v τ i : ℝ)|

def reWt {ι : Type} {N : ℕ} (v : ι → Fin N → ℤ) : ι → Fin N → ℝ := fun τ i => (v τ i : ℝ)

def vDiff (D : D7) (p : ℕ) : ℝ := (padicValNat p (WeightThresholdDefs.dE D) : ℝ) / (Module.finrank ℚ D.host.E : ℝ)

structure Shifts where

  Pe : Finset ℕ

  e : ℕ → ℝ

  C7 : ℝ

  Pa : ℝ

  Pinf : ℝ

  PPe : ℝ

  XW : ℝ

variable {D : D7} (Y : ShimX D.what₂.Tau) {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters}

end GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop.Inhab

open Filter Topology

theorem dividedWeight_unique {ι : Type} {N : ℕ} (W : Wts ι N) (v : ι → Fin N → ℤ) (hk : 1 ≤ W.kc) (hN : W.kc ≤ N) (h : W.IsDiv)
    (h' : Wts.IsDiv { W with u1 := v }) : v = W.u1 := by
  funext τ
  have step : ∀ a c : Fin N, (c : ℕ) = a + 1 → v τ a - W.u1 τ a = v τ c - W.u1 τ c := fun a c hc => by
    have e1 := (h τ).2 a c hc
    have e2 := (h' τ).2 a c hc
    simp only at e2
    omega
  have hN0 : 0 < N := by omega
  have all : ∀ n (hn : n < N), v τ ⟨n, hn⟩ - W.u1 τ ⟨n, hn⟩ = v τ ⟨0, hN0⟩ - W.u1 τ ⟨0, hN0⟩ := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih => intro hn; rw [← ih (by omega)]; exact (step ⟨n, by omega⟩ ⟨n + 1, hn⟩ rfl).symm
  have a1 := (h τ).1 ⟨W.kc - 1, by omega⟩ (by simp only; omega)
  have a2 := (h' τ).1 ⟨W.kc - 1, by omega⟩ (by simp only; omega)
  simp only at a2
  have a3 := all (W.kc - 1) (by omega)
  funext i
  have a4 := all i i.isLt
  simp only [Fin.eta] at a4
  omega

theorem f_pos (D : D7) : 1 ≤ D.R.f := by
  have := D.R.two_le_m
  have := D.R.m_le_f
  show 1 ≤ 2 * D.R.ord
  omega

end GlobalTheory.MeanTop.Inhab
