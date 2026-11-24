module

public import Formalism.LFunctionBounds.ExpSumLowerBound
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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

open Complex

noncomputable section

namespace Formalism.FX

theorem rectRes_ftc_log {γ : ℝ → ℂ} {d : ℂ} {a b : ℝ} (hγ : ∀ t, HasDerivAt γ d t)
    (hs : ∀ t ∈ Set.uIcc a b, γ t ∈ slitPlane) :
    ∫ t in a..b, d / γ t = log (γ b) - log (γ a) := by
  have hc : Continuous γ := continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hγ t).clog_real (hs t ht)) ?_
  refine ContinuousOn.intervalIntegrable ?_
  exact continuousOn_const.div hc.continuousOn fun t ht => Complex.slitPlane_ne_zero (hs t ht)

theorem rectRes_log_sub_log_neg_of_im_pos {z : ℂ} (h : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  have h1 := Complex.arg_neg_eq_arg_sub_pi_of_im_pos h
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]

theorem rectRes_log_sub_log_neg_of_im_neg {z : ℂ} (h : z.im < 0) :
    log z - log (-z) = -((Real.pi : ℂ) * I) := by
  have h1 := Complex.arg_neg_eq_arg_add_pi_of_im_neg h
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]

theorem rectRes_hasDerivAt_horiz (c : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) + c) 1 t := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const c

theorem rectRes_hasDerivAt_vert (c : ℂ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => c + (y : ℂ) * I) I t := by
  simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add c

theorem rectInt_inv_sub (p : ℂ) (x0 x1 y0 y1 : ℝ) (h1 : x0 < p.re) (h2 : p.re < x1)
    (h3 : y0 < p.im) (h4 : p.im < y1) :
    rectInt (fun w => 1 / (w - p)) x0 x1 y0 y1 = 2 * (Real.pi : ℂ) * I := by
  have E : ∀ y : ℝ, y ≠ p.im → ∫ x in x0..x1, 1 / ((x : ℂ) + (y : ℂ) * I - p) =
      log ((x1 : ℂ) + (y : ℂ) * I - p) - log ((x0 : ℂ) + (y : ℂ) * I - p) := by
    intro y hy
    have h := rectRes_ftc_log (γ := fun x : ℝ => (x : ℂ) + ((y : ℂ) * I - p)) (d := 1)
      (a := x0) (b := x1) (fun t => rectRes_hasDerivAt_horiz _ t)
      (fun t _ => Complex.mem_slitPlane_iff.2
        (Or.inr (by intro h'; simp at h'; exact hy (by linarith))))
    simpa only [add_sub_assoc] using h
  have E3 : I * ∫ y in y0..y1, 1 / ((x1 : ℂ) + (y : ℂ) * I - p) =
      log ((x1 : ℂ) + (y1 : ℂ) * I - p) - log ((x1 : ℂ) + (y0 : ℂ) * I - p) := by
    have h := rectRes_ftc_log (γ := fun y : ℝ => ((x1 : ℂ) - p) + (y : ℂ) * I) (d := I)
      (a := y0) (b := y1) (fun t => rectRes_hasDerivAt_vert _ t)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inl (by simp <;> linarith)))
    rw [← intervalIntegral.integral_const_mul, add_sub_right_comm, add_sub_right_comm, ← h]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    show I * (1 / ((x1 : ℂ) + (y : ℂ) * I - p)) = I / (((x1 : ℂ) - p) + (y : ℂ) * I)
    rw [mul_one_div]
    congr 1
    ring
  have E4 : I * ∫ y in y0..y1, 1 / ((x0 : ℂ) + (y : ℂ) * I - p) =
      log (-((x0 : ℂ) + (y1 : ℂ) * I - p)) - log (-((x0 : ℂ) + (y0 : ℂ) * I - p)) := by
    have h := rectRes_ftc_log (γ := fun y : ℝ => -(((x0 : ℂ) - p) + (y : ℂ) * I)) (d := -I)
      (a := y0) (b := y1) (fun t => (rectRes_hasDerivAt_vert _ t).neg)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inl (by simp <;> linarith)))
    rw [← intervalIntegral.integral_const_mul, add_sub_right_comm, add_sub_right_comm, ← h]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    show I * (1 / ((x0 : ℂ) + (y : ℂ) * I - p)) = -I / -(((x0 : ℂ) - p) + (y : ℂ) * I)
    rw [neg_div_neg_eq, mul_one_div]
    congr 1
    ring
  have P1 := rectRes_log_sub_log_neg_of_im_pos (z := (x0 : ℂ) + (y1 : ℂ) * I - p)
    (by simp <;> linarith)
  have P0 := rectRes_log_sub_log_neg_of_im_neg (z := (x0 : ℂ) + (y0 : ℂ) * I - p)
    (by simp <;> linarith)
  unfold rectInt
  beta_reduce
  rw [E y0 h3.ne, E y1 h4.ne', E3, E4]
  linear_combination P1 - P0

theorem rectRes_edge (g G : ℂ → ℂ) (P : Finset ℂ) (b : ℂ → ℂ) (γ : ℝ → ℂ) (a c : ℝ)
    (hγ : Continuous γ) (hG : ContinuousOn (fun t => G (γ t)) (Set.uIcc a c))
    (hP : ∀ t ∈ Set.uIcc a c, ∀ p ∈ P, γ t ≠ p)
    (hg : ∀ w : ℂ, w ∉ P → g w = G w + ∑ p ∈ P, b p / (w - p)) :
    ∫ t in a..c, g (γ t) =
      (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by
  have hγP : ∀ t ∈ Set.uIcc a c, γ t ∉ P := fun t ht hmem => hP t ht _ hmem rfl
  have hcont : ∀ p ∈ P, ContinuousOn (fun t => 1 / (γ t - p)) (Set.uIcc a c) := fun p hp =>
    continuousOn_const.div (hγ.continuousOn.sub continuousOn_const)
      (fun t ht => sub_ne_zero.2 (hP t ht p hp))
  calc ∫ t in a..c, g (γ t)
      = ∫ t in a..c, (G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))) := by
        refine intervalIntegral.integral_congr (fun t ht => ?_)
        show g (γ t) = G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))
        rw [hg _ (hγP t ht)]
        congr 1
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [mul_one_div]
    _ = (∫ t in a..c, G (γ t)) + ∫ t in a..c, ∑ p ∈ P, b p * (1 / (γ t - p)) := by
        refine intervalIntegral.integral_add hG.intervalIntegrable ?_
        exact (continuousOn_finsetSum P (fun p hp => continuousOn_const.mul (hcont p hp))).intervalIntegrable
    _ = (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by
        rw [intervalIntegral.integral_finsetSum]
        · simp_rw [intervalIntegral.integral_const_mul]
        · exact fun p hp => ((hcont p hp).intervalIntegrable).const_mul (b p)

theorem rectRes_sum_combo (P : Finset ℂ) (b A B C D : ℂ → ℂ) :
    ∑ p ∈ P, b p * (A p - B p + I * C p - I * D p) =
      ∑ p ∈ P, b p * A p - ∑ p ∈ P, b p * B p + I * ∑ p ∈ P, b p * C p - I * ∑ p ∈ P, b p * D p := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem rectangle_residue : RectResidue := by
  unfold RectResidue
  intro g G P b x0 x1 y0 y1 _ _ hPin hU hg
  obtain ⟨U, -, hsub, hGd⟩ := hU
  have hGc : ContinuousOn G U := hGd.continuousOn
  have hG0 : ((∫ x in x0..x1, G ((x : ℂ) + (y0 : ℂ) * I)) - (∫ x in x0..x1, G ((x : ℂ) + (y1 : ℂ) * I))
      + I * (∫ y in y0..y1, G ((x1 : ℂ) + (y : ℂ) * I))) - I * (∫ y in y0..y1, G ((x0 : ℂ) + (y : ℂ) * I))
      = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G ⟨x0, y0⟩ ⟨x1, y1⟩
      (hGd.mono hsub)
    simpa only [smul_eq_mul] using h
  have eB := rectRes_edge g G P b (fun x : ℝ => (x : ℂ) + (y0 : ℂ) * I) x0 x1
    (Complex.continuous_ofReal.add continuous_const)
    (hGc.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simpa using ht, by simp⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.im h
      simp at h'
      linarith [(hPin p hp).2.2.1]) hg
  have eT := rectRes_edge g G P b (fun x : ℝ => (x : ℂ) + (y1 : ℂ) * I) x0 x1
    (Complex.continuous_ofReal.add continuous_const)
    (hGc.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simpa using ht, by simp⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.im h
      simp at h'
      linarith [(hPin p hp).2.2.2]) hg
  have eR := rectRes_edge g G P b (fun y : ℝ => (x1 : ℂ) + (y : ℂ) * I) y0 y1
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (hGc.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simp, by simpa using ht⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.re h
      simp at h'
      linarith [(hPin p hp).2.1]) hg
  have eL := rectRes_edge g G P b (fun y : ℝ => (x0 : ℂ) + (y : ℂ) * I) y0 y1
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (hGc.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simp, by simpa using ht⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.re h
      simp at h'
      linarith [(hPin p hp).1]) hg
  have hc := rectRes_sum_combo P b
    (fun p => ∫ t in x0..x1, 1 / ((t : ℂ) + (y0 : ℂ) * I - p))
    (fun p => ∫ t in x0..x1, 1 / ((t : ℂ) + (y1 : ℂ) * I - p))
    (fun p => ∫ t in y0..y1, 1 / ((x1 : ℂ) + (t : ℂ) * I - p))
    (fun p => ∫ t in y0..y1, 1 / ((x0 : ℂ) + (t : ℂ) * I - p))
  have hsum : ∑ p ∈ P, b p * ((∫ t in x0..x1, 1 / ((t : ℂ) + (y0 : ℂ) * I - p))
      - (∫ t in x0..x1, 1 / ((t : ℂ) + (y1 : ℂ) * I - p))
      + I * (∫ t in y0..y1, 1 / ((x1 : ℂ) + (t : ℂ) * I - p))
      - I * (∫ t in y0..y1, 1 / ((x0 : ℂ) + (t : ℂ) * I - p)))
      = 2 * (Real.pi : ℂ) * I * ∑ p ∈ P, b p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have h := rectInt_inv_sub p x0 x1 y0 y1 (hPin p hp).1 (hPin p hp).2.1 (hPin p hp).2.2.1
      (hPin p hp).2.2.2
    unfold rectInt at h
    beta_reduce at h
    rw [h]
    ring
  unfold rectInt
  linear_combination eB - eT + I * eR - I * eL + hG0 + hsum - hc

end Formalism.FX
