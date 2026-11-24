module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFil

theorem dividedPowerFiltration_one_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) : pdP δ 1 ≤ J := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hr, rfl⟩
  induction l with
  | nil => simp at hr
  | cons q t ih =>
    have hq : q.2 ∈ J := hl q (by simp)
    rw [List.map_cons, List.prod_cons]
    by_cases h0 : q.1 = 0
    · refine J.mul_mem_left _ (ih (fun q' h' => hl q' (List.mem_cons_of_mem _ h')) ?_)
      simpa [h0] using hr
    · exact J.mul_mem_right _ (δ.dpow_mem h0 hq)

theorem dividedPowerFiltration_mul_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r r' : ℕ) :
    pdP δ r * pdP δ r' ≤ pdP δ (r + r') := by
  unfold pdP
  rw [Ideal.span_mul_span']
  refine Ideal.span_le.2 ?_
  rintro _ ⟨_, ⟨l, hl, hr, rfl⟩, _, ⟨l', hl', hr', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.1 hq with h | h
    · exact hl q h
    · exact hl' q h
  · simpa using Nat.add_le_add hr hr'
  · simp

theorem dpow_mem_pdP {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (k : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow k x ∈ pdP δ k :=
  Ideal.subset_span ⟨[(k, x)], by simpa using hx, by simp, by simp⟩

theorem isFil_sFil : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)), IsFil (sP Q) (sFil Q) := by
  intro b L Q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr T
    change T.obj.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.obj.pdPow_zero
  · intro T
    change T.obj.pdPow (1 : ℤ).toNat = T.obj.J
    exact le_antisymm (dividedPowerFiltration_one_le T.obj.δ) T.obj.J_le_pdPow_one
  · intro r r' h T
    exact T.obj.pdPow_anti (Int.toNat_le_toNat h)
  · intro r r' T x y hx hy
    have hx' : (show T.obj.B from x) ∈ pdP T.obj.δ r := by
      have : (show T.obj.B from x) ∈ T.obj.pdPow ((r : ℤ).toNat) := hx
      rwa [Int.toNat_natCast] at this
    have hy' : (show T.obj.B from y) ∈ pdP T.obj.δ r' := by
      have : (show T.obj.B from y) ∈ T.obj.pdPow ((r' : ℤ).toNat) := hy
      rwa [Int.toNat_natCast] at this
    have h := dividedPowerFiltration_mul_le T.obj.δ r r' (Ideal.mul_mem_mul hx' hy')
    change _ ∈ T.obj.pdPow (((r + r' : ℕ) : ℤ).toNat)
    rwa [Int.toNat_natCast]
  · intro k T x hx
    change _ ∈ T.obj.pdPow ((k : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact dpow_mem_pdP T.obj.δ k hx

end GlobalTheory.CompanionTheory.DPFil
