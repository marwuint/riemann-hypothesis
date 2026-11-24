module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Module.ZLattice.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

theorem eq_zero_of_norm_real_mul_le {c : ℂ} {C : ℝ} (h : ∀ r : ℝ, ‖(r : ℂ) * c‖ ≤ C) : c = 0 := by
  by_contra hc
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h0 : 0 ≤ C := (norm_nonneg _).trans (h 0)
  have key := h ((C + 1) / ‖c‖)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith) hpos.le), div_mul_cancel₀ _ hpos.ne'] at key
  linarith

theorem entire_sub_conj_bounded_const {φ : ℂ → ℂ} {b : ℂ} {C : ℝ} (hφ : Differentiable ℂ φ)
    (h : ∀ s, ‖φ s - (starRingEnd ℂ) s * b‖ ≤ C) : b = 0 ∧ ∀ s, φ s = φ 0 := by

  have hshift : ∀ a s, φ (s + a) - φ s = φ a - φ 0 := by
    intro a
    have hd : Differentiable ℂ (fun s => φ (s + a) - φ s) :=
      (hφ.comp (differentiable_id.add_const a)).sub hφ
    have hbd : Bornology.IsBounded (Set.range (fun s => φ (s + a) - φ s)) := by
      refine isBounded_iff_forall_norm_le.2 ⟨2 * C + ‖(starRingEnd ℂ) a * b‖, ?_⟩
      rintro _ ⟨s, rfl⟩
      beta_reduce
      have e : φ (s + a) - φ s = ((φ (s + a) - (starRingEnd ℂ) (s + a) * b)
          - (φ s - (starRingEnd ℂ) s * b)) + (starRingEnd ℂ) a * b := by
        rw [map_add (f := _)]; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      gcongr
      exact (norm_sub_le _ _).trans (by linarith [h (s + a), h s])
    intro s
    simpa [zero_add] using hd.apply_eq_apply_of_bounded hbd s 0

  have hderiv : ∀ s, deriv φ s = deriv φ 0 := fun s => by
    have e1 : (fun x => φ (x + s)) = fun x => φ x + (φ s - φ 0) := by
      funext x
      linear_combination hshift s x
    simpa only [deriv_comp_add_const, deriv_add_const, zero_add] using
      congrArg (fun f => deriv f 0) e1

  obtain ⟨β, hlin⟩ : ∃ β : ℂ, ∀ s, φ s = φ 0 + β * s := by
    refine ⟨deriv φ 0, fun s => ?_⟩
    have hz : ∀ x, deriv (fun s => φ s - deriv φ 0 * s) x = 0 := fun x => by
      have hx : HasDerivAt (fun s => φ s - deriv φ 0 * s) _ x :=
        (hφ x).hasDerivAt.sub ((hasDerivAt_id' x).const_mul _)
      rw [hx.deriv, hderiv x]
      ring
    linear_combination is_const_of_deriv_eq_zero (f := fun s => φ s - deriv φ 0 * s)
      (hφ.sub (differentiable_fun_id.const_mul _)) hz s 0

  have hB : ∀ s, ‖β * s - (starRingEnd ℂ) s * b‖ ≤ C + ‖φ 0‖ := fun s => by
    have e : β * s - (starRingEnd ℂ) s * b = (φ s - (starRingEnd ℂ) s * b) - φ 0 := by
      rw [hlin s]; ring
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith [h s])
  have h1 : β - b = 0 := eq_zero_of_norm_real_mul_le fun r => by
    have hr := hB r
    rw [Complex.conj_ofReal] at hr
    exact Eq.trans_le (by congr 1; ring) hr
  have h2 : Complex.I * (β + b) = 0 := eq_zero_of_norm_real_mul_le fun r => by
    have hr := hB (r * Complex.I)
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I] at hr
    exact Eq.trans_le (by congr 1; ring) hr
  have h3 : β + b = 0 := (mul_eq_zero.mp h2).resolve_left Complex.I_ne_zero
  have hβ : β = 0 := by linear_combination (h1 + h3) / 2
  refine ⟨by linear_combination (h3 - h1) / 2, fun s => ?_⟩
  rw [hlin s, hβ, zero_mul, add_zero]

theorem entire_antilinear_periods_const :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (v : (Fin g → ℂ) → ℂ) (t : (Fin g → ℂ)), Differentiable ℂ v →
        (∀ (l : Λ) z, v (z + l) = v z + t ⬝ᵥ star (l : (Fin g → ℂ))) →
        t = 0 ∧ ∀ z, v z = v 0 := by
  intro g Λ hdisc hspan v t hv hper
  have : IsZLattice ℝ Λ := ⟨hspan⟩

  have hcont : Continuous (fun z => v z - t ⬝ᵥ star z) :=
    hv.continuous.sub (continuous_const.dotProduct continuous_star)
  have hperw : ∀ z w, w ∈ Λ → (fun z => v z - t ⬝ᵥ star z) (z + w) = (fun z => v z - t ⬝ᵥ star z) z := by
    intro z w hw
    simp only
    rw [hper ⟨w, hw⟩ z, star_add, dotProduct_add]
    ring
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (IsZLattice.isCompact_range_of_periodic Λ _ hcont hperw).isBounded

  have hline : ∀ d : Fin g → ℂ, t ⬝ᵥ star d = 0 ∧ ∀ s : ℂ, v (s • d) = v 0 := by
    intro d
    have hd : Differentiable ℂ (fun s : ℂ => v (s • d)) :=
      hv.comp (differentiable_id.smul_const d)
    have hb : ∀ s : ℂ, ‖v (s • d) - (starRingEnd ℂ) s * (t ⬝ᵥ star d)‖ ≤ M := by
      intro s
      have e : (starRingEnd ℂ) s * (t ⬝ᵥ star d) = t ⬝ᵥ star (s • d) := by
        rw [star_smul, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
      rw [e]
      exact hM _ ⟨s • d, rfl⟩
    obtain ⟨h1, h2⟩ := entire_sub_conj_bounded_const hd hb
    exact ⟨h1, fun s => by simpa using h2 s⟩
  refine ⟨?_, fun z => by simpa using (hline z).2 1⟩
  funext i
  have hi := (hline (Pi.single i 1)).1
  rw [← Pi.single_star, star_one, dotProduct_single, mul_one] at hi
  simpa using hi

end GlobalTheory
