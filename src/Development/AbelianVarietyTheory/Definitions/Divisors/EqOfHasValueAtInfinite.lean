module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix

noncomputable section
namespace GlobalTheory.LGrp

section Rational
open Polynomial

def IsLaurentPoly (R : RatFunc ℂ) : Prop :=
  ∃ (m : ℕ) (p : ℂ[X]), R * RatFunc.X ^ m = algebraMap _ _ p

def lFactor (S : Multiset ℂˣ) : RatFunc ℂ := (S.map fun a : ℂˣ => (1 - RatFunc.C (a : ℂ) * RatFunc.X)⁻¹).prod

end Rational

section ZetaNonvanishing₂
open ValuativeRel GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

variable [MeasurableSpace (GL n k)]

variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ}

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in
private theorem valuation_det_le_one_of_entries_integer {y : GL n k}
    (h : ∀ i j, (y : Matrix n n k) i j ∈ (valuation k).integer) :
    valuation k (GeneralLinearGroup.det y : k) ≤ 1 := by
  set A : Matrix n n (valuation k).integer := Matrix.of fun i j => ⟨(y : Matrix n n k) i j, h i j⟩
  have e : (y : Matrix n n k) = ((valuation k).integer.subtype).mapMatrix A := by
    ext i j
    rfl
  have hd : (GeneralLinearGroup.det y : k) = (valuation k).integer.subtype A.det := by
    rw [GeneralLinearGroup.val_det_apply, RingHom.map_det, ← e]
  rw [hd]
  exact (Valuation.mem_integer_iff _ _).mp (SetLike.coe_mem _)


open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in
theorem _root_.GlobalTheory.LGrp.nabs_det_of_mem_KO {x : GL n k}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det x) = 1 := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hx
  apply _root_.GlobalTheory.SmGL.nabs_eq_one
  have h1 := valuation_det_le_one_of_entries_integer hx.1
  have h2 := valuation_det_le_one_of_entries_integer hx.2
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at h2
  have hpos : 0 < valuation k (GeneralLinearGroup.det x : k) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
private theorem smGL_ord_pow_eq_mul (x : kˣ) (m : ℕ) :
    _root_.GlobalTheory.SmGL.ord k (x ^ m) = m * _root_.GlobalTheory.SmGL.ord k x := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
  | succ m ih =>
    rw [pow_succ, _root_.GlobalTheory.SmGL.ord_mul, ih]
    push_cast
    ring

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
private theorem exists_unit_ord_eq_one_and_nabs_eq_inv_resCard :
    ∃ ϖ : kˣ, _root_.GlobalTheory.SmGL.ord k ϖ = 1 ∧
      _root_.GlobalTheory.SplitWeil.nabs k ϖ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ)⁻¹ := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (valuation k).integer
  have hp0 : (p : k) ≠ 0 := fun h => hp.ne_zero (Subtype.ext h)
  obtain ⟨y, hy⟩ : ∃ y : k, valuation k y = uniformizer k := valuation_surjective _
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact (uniformizer_pos (R := k)).ne hy
  have hyint : y ∈ (valuation k).integer := by
    rw [Valuation.mem_integer_iff, hy]
    exact uniformizer_lt_one.le
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨y, hyint⟩ : (valuation k).integer)) (fun h => hy0 (congrArg Subtype.val h)) hp
  have hu0 : ((u : (valuation k).integer) : k) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  refine ⟨Units.mk0 (p : k) hp0, ?_, _root_.GlobalTheory.SplitWeil.nabs_uniformiser hp rfl⟩
  have hyo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 y hy0) = 1 :=
    _root_.GlobalTheory.SmGL.ord_eq_one hy
  have huo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 _ hu0) = 0 := by
    apply _root_.GlobalTheory.SmGL.ord_eq_zero
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
  have hsplit : Units.mk0 y hy0 = Units.mk0 _ hu0 * Units.mk0 (p : k) hp0 ^ m := by
    ext
    have := congrArg Subtype.val hu
    simpa using this
  rw [hsplit, _root_.GlobalTheory.SmGL.ord_mul, huo, smGL_ord_pow_eq_mul,
    zero_add] at hyo
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hyo with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2
  · omega


open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in
theorem _root_.GlobalTheory.LGrp.nabs_eq_zpow (x : kˣ) :
    _root_.GlobalTheory.SplitWeil.nabs k x =
      (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-_root_.GlobalTheory.SmGL.ord k x) := by
  obtain ⟨ϖ, hord, habs⟩ := exists_unit_ord_eq_one_and_nabs_eq_inv_resCard (k := k)
  have hq : (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ≠ 0 := by
    have := _root_.GlobalTheory.SplitWeil.one_lt_resCard k
    positivity
  have hinv : _root_.GlobalTheory.SplitWeil.nabs k ϖ⁻¹ = _root_.GlobalTheory.SplitWeil.resCard k := by
    have h := _root_.GlobalTheory.SplitWeil.nabs_mul k ϖ ϖ⁻¹
    rw [mul_inv_cancel, _root_.GlobalTheory.SplitWeil.nabs_one, habs] at h
    exact ((inv_mul_eq_one₀ hq).mp h.symm).symm
  have oinv : _root_.GlobalTheory.SmGL.ord k ϖ⁻¹ = -1 := by
    have h := _root_.GlobalTheory.SmGL.ord_mul k ϖ ϖ⁻¹
    rw [mul_inv_cancel, hord,
      _root_.GlobalTheory.SmGL.ord_eq_zero (x := (1 : kˣ)) (by simp only [Units.val_one, map_one])] at h
    omega
  have key : ∀ m : ℤ, _root_.GlobalTheory.SplitWeil.nabs k (ϖ ^ m) =
      (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) ∧ _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
    intro m
    refine Int.induction_on m ?_ ?_ ?_
    · refine ⟨by simp [_root_.GlobalTheory.SplitWeil.nabs_one], ?_⟩
      rw [zpow_zero]
      exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
    · intro i ih
      rw [_root_.zpow_add_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
        ih.1, ih.2, habs, hord]
      refine ⟨?_, rfl⟩
      rw [neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
    · intro i ih
      rw [_root_.zpow_sub_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
        ih.1, ih.2, hinv, oinv]
      refine ⟨?_, by ring⟩
      rw [show -(-(i : ℤ) - 1) = -(-(i : ℤ)) + 1 by ring, zpow_add₀ hq, _root_.zpow_one]
  set o := _root_.GlobalTheory.SmGL.ord k x
  have hy : _root_.GlobalTheory.SmGL.ord k (x * ϖ ^ (-o)) = 0 := by
    rw [_root_.GlobalTheory.SmGL.ord_mul, (key _).2]
    ring
  have hy1 : _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o)) = 1 :=
    _root_.GlobalTheory.SmGL.nabs_eq_one k
      (_root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp hy)
  have hx : x * ϖ ^ (-o) * ϖ ^ o = x := by
    rw [mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
  calc _root_.GlobalTheory.SplitWeil.nabs k x
      = _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o) * ϖ ^ o) := by rw [hx]
    _ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-o) := by
      rw [_root_.GlobalTheory.SplitWeil.nabs_mul, hy1, (key o).1, one_mul]


end ZetaNonvanishing₂

end GlobalTheory.LGrp
