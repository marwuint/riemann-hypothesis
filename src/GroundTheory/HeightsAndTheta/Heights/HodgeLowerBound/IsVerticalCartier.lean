import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Values

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def IsValueAt (y : (Σ k, ι k) → Ω) (a : Ω) (z : (Σ k, ι k) → ℂ) (v : ℂ) : Prop :=
  ∃ (d : κ → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval y h ≠ 0 ∧
    aeval y g = a * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
    eval z (map (Int.castRingHom ℂ) g) = v * eval z (map (Int.castRingHom ℂ) h)

def RegularAt (y : (Σ k, ι k) → Ω) (a : Ω) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∃ v, IsValueAt y a z v

open Classical in

def valAt (y : (Σ k, ι k) → Ω) (a : Ω) (z : (Σ k, ι k) → ℂ) : ℂ :=
  if h : RegularAt y a z then h.choose else 0

end Values

section Frames

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
  {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def IsLocSection (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (NumbersDVR.segreVec y) N E)
    (z : (Σ k, ι k) → ℂ) (e : E) : Prop :=
  ∃ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) ∧ ∃ (m : ℕ) (a : Fin m → Ω) (s : Fin m → E),
    (∀ l, s l ∈ W.lat c) ∧ (∀ l, RegularAt y (a l) z) ∧ e = ∑ l, a l • s l

def IsFrameAt (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (NumbersDVR.segreVec y) N E)
    (z : (Σ k, ι k) → ℂ) (b : Fin N → E) : Prop :=
  (∀ q, IsLocSection y W z (b q)) ∧
    ∀ e, IsLocSection y W z e → ∃ a : Fin N → Ω, (∀ q, RegularAt y (a q) z) ∧ e = ∑ q, a q • b q

end Frames

section Charts

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

structure SncChart (y : (Σ k, ι k) → Ω) (bd : Ideal (MRing ι)) (n : ℕ) where

  c : ∀ k, ι k

  φ : (Fin n → ℂ) → (Σ k, ι k) → ℂ

  kb : ℕ
  kb_le : kb ≤ n

  z : Fin n → Ω
  mem : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1, φ w ∈ mcPts (mCoordIdeal y)
  normalised : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ k, φ w ⟨k, c k⟩ = 1
  holo : AnalyticOnNhd ℂ φ (Metric.ball 0 1)
  coord : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, IsValueAt y (z i) (φ w) (w i)
  isOpen_image : ∃ O : Set ((Σ k, ι k) → ℂ), IsOpen O ∧
    φ '' Metric.ball 0 1 = O ∩ {x | x ∈ mcPts (mCoordIdeal y) ∧ ∀ k, x ⟨k, c k⟩ = 1}
  boundary : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1,
    φ w ∈ mcPts bd ↔ ∃ i : Fin n, (i : ℕ) < kb ∧ w i = 0

end Charts

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
