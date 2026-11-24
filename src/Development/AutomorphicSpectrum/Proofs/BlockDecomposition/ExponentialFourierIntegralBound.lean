module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
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
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem integral_exp_neg_mul_abs {ε : ℝ} (hε : 0 < ε) :
    ∫ u : ℝ, Real.exp (-ε * |u|) = 2 / ε := by
  have h := integral_comp_abs (f := fun x => Real.exp (-ε * x))
  rw [h, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero]
  field_simp

theorem integrable_exp_neg_mul_abs {ε : ℝ} (hε : 0 < ε) :
    Integrable fun u : ℝ => Real.exp (-ε * |u|) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_neg_mul_abs hε]
  positivity

theorem integrable_and_norm_integral_le (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X]
    (φ : ℝ × ℝ → X) (l : ℂ × ℂ) (ε M : ℝ) (hε : 0 < ε) (hφ : Continuous φ)
    (hb : ∀ t : ℝ × ℝ, ‖φ t‖ ≤ M * Real.exp (-rdot (l.1.re, l.2.re) t) *
      Real.exp (-ε * (|t.1| + |t.2|))) :
    Integrable (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) ∧
      ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖ ≤ M * (2 / ε) ^ 2 := by
  have hg1 := integrable_exp_neg_mul_abs hε
  have hgi : Integrable (fun t : ℝ × ℝ => M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|))) :=
    (hg1.mul_prod hg1).const_mul M
  have hbound : ∀ t : ℝ × ℝ, ‖Complex.exp (dot l t) • φ t‖ ≤
      M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) := by
    intro t
    rw [norm_smul, Complex.norm_exp,
      show (dot l t).re = rdot (l.1.re, l.2.re) t by simp [dot, rdot]]
    have h1 : Real.exp (rdot (l.1.re, l.2.re) t) * Real.exp (-rdot (l.1.re, l.2.re) t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    refine (mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le).trans_eq ?_
    rw [mul_add, Real.exp_add]
    linear_combination (M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|))) * h1
  have hc : Continuous (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) := by
    simp only [dot]
    fun_prop
  refine ⟨hgi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound), ?_⟩
  refine (norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hbound)).trans_eq ?_
  rw [integral_const_mul, Measure.volume_eq_prod,
    integral_prod_mul (fun u : ℝ => Real.exp (-ε * |u|)) (fun u : ℝ => Real.exp (-ε * |u|)),
    integral_exp_neg_mul_abs hε]
  ring

end GlobalTheory.CompanionTheory.TubeFourier
