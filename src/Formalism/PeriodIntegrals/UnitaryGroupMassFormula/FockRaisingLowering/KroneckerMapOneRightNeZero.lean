module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.SameSign
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

noncomputable section

open Matrix

namespace FockRL

def jsgn {p q : ℕ} : FockH1Action.Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem Jm_eq_diagonal (p q : ℕ) : FockH1Action.Jm p q = Matrix.diagonal (jsgn (p := p) (q := q)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [FockH1Action.Jm, FockH1Action.Jpq, jsgn,
      Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp_all

theorem conjR_apply {p q : ℕ} (Z : FockH1Action.Mat p q) (a b : FockH1Action.Ix p q) :
    FockH1Action.conjR Z a b = -(jsgn a * star (Z b a) * jsgn b) := by
  simp only [FockH1Action.conjR, FockH1Action.adjZ,
    Jm_eq_diagonal, Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply]

theorem conjR_apply_of_not {p q : ℕ} (Z : FockH1Action.Mat p q) {a b : FockH1Action.Ix p q}
    (h : ¬ FockH1Action.sameBlock a b) : FockH1Action.conjR Z a b = (starRingEnd ℂ) (Z b a) := by
  rw [conjR_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [FockH1Action.sameBlock, jsgn]

theorem sameBlock_symm {p q : ℕ} {a b : FockH1Action.Ix p q} (h : FockH1Action.sameBlock a b) :
    FockH1Action.sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [FockH1Action.sameBlock]

theorem conjR_isPC {p q : ℕ} (Z : FockH1Action.Mat p q) (hZ : FockH1Action.IsPC Z) :
    FockH1Action.IsPC (FockH1Action.conjR Z) := by
  intro a b hab
  rw [conjR_apply, hZ b a (sameBlock_symm hab)]
  simp

theorem linePos_left {p q r s : ℕ} (a a' : FockH1Action.Ix p q) (b : FockH1Action.Ix r s) :
    FockH1Action.linePos ((a, b) : FockH1Action.Ln p q r s) = FockH1Action.linePos ((a', b) : FockH1Action.Ln p q r s) ↔
      FockH1Action.sameBlock a a' := by
  rcases a with a | a <;> rcases a' with a' | a' <;> rcases b with b | b <;>
    simp [FockH1Action.linePos, FockH1Action.sameBlock]

theorem linePos_right {p q r s : ℕ} (a : FockH1Action.Ix p q) (b b' : FockH1Action.Ix r s) :
    FockH1Action.linePos ((a, b) : FockH1Action.Ln p q r s) = FockH1Action.linePos ((a, b') : FockH1Action.Ln p q r s) ↔
      FockH1Action.sameBlock b b' := by
  rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
    simp [FockH1Action.linePos, FockH1Action.sameBlock]

theorem fockAct1_eq (p q r s : ℕ) (Z : FockH1Action.Mat p q) : FockH1Action.fockAct1 p q r s Z =
    FockH1Action.omAct p q r s (Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s)) := by
  rfl

theorem fockAct2_eq (p q r s : ℕ) (Z : FockH1Action.Mat r s) : FockH1Action.fockAct2 p q r s Z =
    FockH1Action.omAct p q r s (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z) := by
  rfl

theorem kroneckerMap_one_right_ne_zero {p q r s : ℕ} (Z : FockH1Action.Mat p q) {a a' : FockH1Action.Ix p q} {b b' : FockH1Action.Ix r s}
    (h : Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s) (a, b) (a', b') ≠ 0) :
    Z a a' ≠ 0 ∧ b = b' := by
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with hb
  · exact ⟨by simpa using h, hb⟩
  · simp at h

theorem kroneckerMap_one_left_ne_zero {p q r s : ℕ} (Z : FockH1Action.Mat r s) {a a' : FockH1Action.Ix p q} {b b' : FockH1Action.Ix r s}
    (h : Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z (a, b) (a', b') ≠ 0) :
    Z b b' ≠ 0 ∧ a = a' := by
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with ha
  · exact ⟨by simpa using h, ha⟩
  · simp at h

theorem kroneckerProperties : MatStep := by
  intro p q r s
  refine ⟨fockAct1_eq p q r s, fockAct2_eq p q r s, ?_, ?_, ?_, ?_,
    conjR_isPC, conjR_isPC, ?_, ?_⟩
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_right_ne_zero Z h
    exact (linePos_left a a' b).2 (Classical.byContradiction fun hn => hz (hZ a a' hn))
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_left_ne_zero Z h
    exact (linePos_right a b b').2 (Classical.byContradiction fun hn => hz (hZ b b' hn))
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h heq
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_right_ne_zero Z h
    exact hz (hZ a a' ((linePos_left a a' b).1 heq))
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h heq
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_left_ne_zero Z h
    exact hz (hZ b b' ((linePos_right a b b').1 heq))
  · rintro Z ⟨a, b⟩ ⟨a', b'⟩ h1 h2
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases hb : b = b'
    · subst hb
      have hn : ¬ FockH1Action.sameBlock a' a := fun hs => by
        have := (linePos_left a a' b).2 (sameBlock_symm hs)
        simp [h1, h2] at this
      simp [conjR_apply_of_not Z hn]
    · simp [hb, Ne.symm hb]
  · rintro Z ⟨a, b⟩ ⟨a', b'⟩ h1 h2
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases ha : a = a'
    · subst ha
      have hn : ¬ FockH1Action.sameBlock b' b := fun hs => by
        have := (linePos_right a b b').2 (sameBlock_symm hs)
        simp [h1, h2] at this
      simp [conjR_apply_of_not Z hn]
    · simp [ha, Ne.symm ha]

end FockRL
