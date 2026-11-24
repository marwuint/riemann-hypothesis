module

public import Formalism.SatakeDualWeyl.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Formalism.UG

namespace GlobalTheory.DualFrames

variable {A : Type} [CommRing A] {k : ℕ}

theorem hform_eq_dot (τ : A →+* A) (J : Matrix (Fin k) (Fin k) A) (x y : Fin k → A) :
    hform τ J x y = (τ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  unfold hform
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_frames (τ : A →+* A) (J B C : Matrix (Fin k) (Fin k) A)
    (h : cT τ B * J * C = 1) (x y : Fin k → A) :
    hform τ J (B *ᵥ x) (C *ᵥ y) = ∑ i, τ (x i) * y i := by
  rw [hform_eq_dot]
  have hmap : (τ ∘ (B *ᵥ x)) = (B.map τ) *ᵥ (τ ∘ x) := by
    funext i

    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hct : (B.map τ)ᵀ = cT τ B := by
    unfold cT
    rfl
  rw [hmap, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hct, h, Matrix.one_mulVec]
  simp [dotProduct]

theorem hform_swap (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) (J : Matrix (Fin k) (Fin k) A)
    (hJ : IsHerm τ J) (x y : Fin k → A) : τ (hform τ J x y) = hform τ J y x := by
  unfold IsHerm cT at hJ
  have hJ' : ∀ i j, τ (J i j) = J j i := by
    intro i j
    simpa using congrFun (congrFun hJ j) i
  unfold hform

  simp only [map_sum, map_mul, hτ, hJ']
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_mulVec (B : GL (Fin k) A) (y : Fin k → A) :
    ∃ z, (B : Matrix (Fin k) (Fin k) A) *ᵥ z = y := by
  refine ⟨((B⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) *ᵥ y, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem dual_of_dual_frames :
    ∀ (A : Type) [CommRing A] (S : Subring A) (τ : A →+* A), (∀ a, τ (τ a) = a) →
      (∀ a ∈ S, τ a ∈ S) → ∀ (k : ℕ) (J : Matrix (Fin k) (Fin k) A), IsHerm τ J →
      ∀ (B C : GL (Fin k) A) (L₁ L₂ : Submodule S (Fin k → A)),
      cT τ (B : Matrix (Fin k) (Fin k) A) * J * (C : Matrix (Fin k) (Fin k) A) = 1 →
      (∀ y : Fin k → A, (B : Matrix (Fin k) (Fin k) A) *ᵥ y ∈ L₁ ↔ ∀ i, y i ∈ S) →
      (∀ y : Fin k → A, (C : Matrix (Fin k) (Fin k) A) *ᵥ y ∈ L₂ ↔ ∀ i, y i ∈ S) →
      (∀ y, y ∈ L₂ ↔ ∀ x ∈ L₁, hform τ J x y ∈ S) ∧
      (∀ y, y ∈ L₁ ↔ ∀ x ∈ L₂, hform τ J x y ∈ S) ∧
      (∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform τ J x y ∈ S) := by
  intro A _ S τ hτ hS k J hJ B C L₁ L₂ h hL₁ hL₂

  have pair := hform_frames τ J B C h
  have flip := fun x y => (hform_swap τ hτ J hJ y x).symm
  have memS_iff : ∀ a, τ a ∈ S ↔ a ∈ S := fun a =>
    ⟨fun ha => hτ a ▸ hS _ ha, hS a⟩
  have single_mem : ∀ i j, (Pi.single i (1 : A) : Fin k → A) j ∈ S := by
    intro i j
    by_cases hj : j = i <;> simp [hj, S.zero_mem]
  have coord : ∀ u v : Fin k → A, (∀ i, u i ∈ S) → (∀ i, v i ∈ S) → ∑ i, τ (u i) * v i ∈ S :=
    fun u v hu hv => sum_mem fun i _ => mul_mem (hS _ (hu i)) (hv i)
  have part1 : ∀ y, y ∈ L₂ ↔ ∀ x ∈ L₁, hform τ J x y ∈ S := by
    intro y
    obtain ⟨v, rfl⟩ := exists_mulVec C y
    rw [hL₂]
    refine ⟨fun hv x hx => ?_, fun hall i => ?_⟩
    · obtain ⟨u, rfl⟩ := exists_mulVec B x
      rw [pair]
      exact coord u v ((hL₁ u).1 hx) hv
    · have key := hall ((B : Matrix (Fin k) (Fin k) A) *ᵥ Pi.single i 1) ((hL₁ _).2 (single_mem i))
      have e : ∑ j, τ ((Pi.single i (1 : A) : Fin k → A) j) * v j = v i := by
        simp [Pi.single_apply]
      rwa [pair, e] at key
  have part2 : ∀ y, y ∈ L₁ ↔ ∀ x ∈ L₂, hform τ J x y ∈ S := by
    intro y
    obtain ⟨v, rfl⟩ := exists_mulVec B y
    rw [hL₁]
    refine ⟨fun hv x hx => ?_, fun hall i => ?_⟩
    · obtain ⟨u, rfl⟩ := exists_mulVec C x
      rw [flip, pair, memS_iff]
      exact coord v u hv ((hL₂ u).1 hx)
    · have key := hall ((C : Matrix (Fin k) (Fin k) A) *ᵥ Pi.single i 1) ((hL₂ _).2 (single_mem i))
      have e : ∑ j, τ (v j) * (Pi.single i (1 : A) : Fin k → A) j = τ (v i) := by
        simp [Pi.single_apply]
      rwa [flip, pair, memS_iff, e, memS_iff] at key
  have part3 : ∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform τ J x y ∈ S := fun x =>
    (part2 x).trans (forall₂_congr fun y _ => by rw [flip x y, memS_iff])
  exact ⟨part1, part2, part3⟩

end GlobalTheory.DualFrames
