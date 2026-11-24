module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Set.Card
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
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Finset

namespace GlobalTheory

theorem summable_and_tsum_le_of_box_count (ι Γ : Type) [Fintype ι] (D : Γ → ι → ℝ) (t : Γ → ℝ)
    (a A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (ha : Real.exp (-a) ≤ 1 / 2) (_hD : ∀ γ v, 0 ≤ D γ v)
    (ht : ∀ γ, 0 ≤ t γ ∧ t γ ≤ c * ∏ v, Real.exp (-(2 * a * (⌊D γ v⌋₊ : ℝ))))
    (hN : ∀ r : ι → ℝ, (∀ v, 0 ≤ r v) → {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.Finite ∧
      (({γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.ncard : ℕ) : ℝ) ≤ A * Real.exp (a * ∑ v, r v)) :
    Summable t ∧ ∑' γ, t γ ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by
  classical
  set q := Real.exp (-a) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hgeom : ∀ M : ℕ, ∑ k ∈ Finset.range M, q ^ k ≤ 2 := fun M =>
    (Finset.sum_le_sum fun k _ => pow_le_pow_left₀ hq0 ha k).trans (sum_geometric_two_le M)
  have hprod : ∀ F : Finset (ι → ℕ), ∑ n ∈ F, ∏ v, q ^ (n v) ≤ 2 ^ Fintype.card ι := by
    intro F
    set M := F.sup (fun n => ∑ v, n v) + 1 with hM
    have hsub : F ⊆ Fintype.piFinset (fun _ : ι => Finset.range M) := by
      intro n hn
      refine Fintype.mem_piFinset.2 fun v => Finset.mem_range.2 ?_
      have h1 : n v ≤ ∑ w, n w :=
        Finset.single_le_sum (fun w _ => Nat.zero_le (n w)) (Finset.mem_univ v)
      have h2 : ∑ w, n w ≤ F.sup (fun n => ∑ v, n v) := Finset.le_sup (f := fun n => ∑ v, n v) hn
      omega
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun n _ _ => Finset.prod_nonneg fun v _ => pow_nonneg hq0 _).trans ?_
    rw [← Finset.prod_univ_sum (fun _ : ι => Finset.range M) (fun _ k => q ^ k)]
    exact (Finset.prod_le_prod₀ (fun v _ => Finset.sum_nonneg fun k _ => pow_nonneg hq0 k)
      fun v _ => hgeom M).trans_eq (by simp)
  have hB : 0 ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by positivity
  have hfin : ∀ s : Finset Γ, ∑ γ ∈ s, t γ ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by
    intro s
    set φ : Γ → ι → ℕ := fun γ v => ⌊D γ v⌋₊ with hφ
    set s' := s.filter (fun γ => t γ ≠ 0) with hs'
    rw [← Finset.sum_filter_ne_zero, ← Finset.sum_fiberwise_of_maps_to (t := s'.image φ) (g := φ)
      (fun γ hγ => Finset.mem_image_of_mem φ hγ)]
    have hfib : ∀ n : ι → ℕ, ∑ γ ∈ s'.filter (fun γ => φ γ = n), t γ ≤
        c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) := by
      intro n
      set Fn := s'.filter (fun γ => φ γ = n) with hFn
      set e : ℝ := c * ∏ v, Real.exp (-(2 * a * (n v : ℝ))) with he_def
      have he : 0 ≤ e := by positivity
      have h1 : ∑ γ ∈ Fn, t γ ≤ Fn.card * e := by
        refine (Finset.sum_le_card_nsmul Fn t e fun γ hγ => ?_).trans_eq (nsmul_eq_mul _ _)
        have hfl : ∀ v, ⌊D γ v⌋₊ = n v := fun v => congrFun (Finset.mem_filter.1 hγ).2 v
        simpa only [hfl] using (ht γ).2
      set r : ι → ℝ := fun v => (n v : ℝ) + 1 with hr_def
      have hr : ∀ v, 0 ≤ r v := fun v => by positivity
      obtain ⟨hSf, hSc⟩ := hN r hr
      have hsub : (↑Fn : Set Γ) ⊆ {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v} := by
        intro γ hγ
        have hm := Finset.mem_filter.1 (Finset.mem_coe.1 hγ)
        have hm' := Finset.mem_filter.1 hm.1
        refine ⟨hm'.2, fun v => ?_⟩
        have hfl : ⌊D γ v⌋₊ = n v := congrFun hm.2 v
        have hl := Nat.lt_floor_add_one (D γ v)
        rw [hfl] at hl
        exact hl.le
      have hcard : (Fn.card : ℝ) ≤ A * Real.exp (a * ∑ v, r v) := by
        have hc' := (Set.ncard_coe_finset Fn).symm.trans_le (Set.ncard_le_ncard hsub hSf)
        exact le_trans (by exact_mod_cast hc') hSc
      have hS1 : ∑ v, r v = ∑ v, (n v : ℝ) + Fintype.card ι := by
        simp only [hr_def, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]
      refine h1.trans ((mul_le_mul_of_nonneg_right hcard he).trans_eq ?_)
      rw [he_def, hq]
      simp_rw [← Real.exp_nat_mul]
      rw [← Real.exp_sum, ← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, hS1]
      rw [show A * Real.exp (a * (∑ v, (n v : ℝ) + Fintype.card ι)) *
            (c * Real.exp (-(2 * a * ∑ v, (n v : ℝ)))) =
          c * A * (Real.exp (a * (∑ v, (n v : ℝ) + Fintype.card ι)) *
            Real.exp (-(2 * a * ∑ v, (n v : ℝ)))) by ring,
        show c * A * Real.exp (a * Fintype.card ι) * Real.exp ((∑ v, (n v : ℝ)) * -a) =
          c * A * (Real.exp (a * Fintype.card ι) * Real.exp ((∑ v, (n v : ℝ)) * -a)) by ring,
        ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    refine (Finset.sum_le_sum fun n _ => hfib n).trans ?_
    rw [← Finset.mul_sum]
    refine (mul_le_mul_of_nonneg_left (hprod _) (by positivity)).trans_eq ?_
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm (Fintype.card ι : ℝ) a]
    ring
  exact ⟨summable_of_sum_le (fun γ => (ht γ).1) hfin, tsum_le_of_sum_le' hB hfin⟩

end GlobalTheory
