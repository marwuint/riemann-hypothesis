module

public import Formalism.PieriBlockIdeals.BranchingBoundLastGradedOneRow
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
public import Formalism.PieriBlockIdeals.PieriColumnMinors.DividedPowerZeroZeroVector
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open MvPolynomial

namespace Formalism.CohomologicalDescent.LD

open Formalism.GradedWeylDivisibility

theorem lastGradedImpliesLast : LastGradedImpliesLast := by
  intro h l p q w M lam2 hl ha hw eL heL i μ hd
  have h0 : Antitone (0 : Fin (q + p) → ℤ) := fun _ _ _ => le_rfl
  refine h l p q w M lam2 0 hl ha hw h0 0 eL (fun μ2 _ => heL μ2) i μ hd ?_
  simp [depth2]

theorem last_graded_implies_one_block' : OneRowBoundOfLastGraded :=
  fun h l q w M lam2 ξ hl ha hw hξ => h l 1 q w M lam2 ξ hl ha hw hξ

theorem depth2Levi : Depth2Levi := by
  intro p q w lam2 μ2 ξ
  unfold depth2 blockWtLast
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem depth_two_block_eq_sum_diff (p q w : ℕ) (lam2 : Fin q → ℕ) (μ : Fin (q + p) → ℕ) :
    depth2 (fun a : Fin (q + p) => if a.val < q then 1 else 0) (blockWtLast p q w lam2) μ =
      ((∑ b, lam2 b : ℕ) : ℤ) - ((∑ b : Fin q, μ (Fin.castAdd p b) : ℕ) : ℤ) := by
  unfold depth2 blockWtLast
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Finset.sum_sub_distrib]

theorem sum_block_weight_last (p q w : ℕ) (lam2 : Fin q → ℕ) :
    ∑ a, blockWtLast p q w lam2 a = ∑ b, lam2 b + p * w := by
  unfold blockWtLast
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem depthLastIff : DepthLastIff := by
  intro p q w i lam2 μ hsum
  rw [depth_two_block_eq_sum_diff, sum_block_weight_last, Fin.sum_univ_add] at *
  unfold IsDepthLast
  generalize p * w = pw at *
  omega

theorem depth2Dual : Depth2Dual := by
  intro r M ξ lam μ hl hm
  constructor
  · unfold depth2
    rw [← Equiv.sum_comp Fin.revPerm fun a => ξ a * ((lam a : ℤ) - (μ a : ℤ))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.cast_sub (hl _), Nat.cast_sub (hm _)]
    simp only [Fin.revPerm_apply]
    ring
  · exact fun hξ a b hab => neg_le_neg (hξ (Fin.rev_le_rev.mpr hab))

theorem dominance_of_nabla_weight (r : ℕ) (ν μ : Fin r → ℕ) (hν : Antitone ν) (x : MvPolynomial (Fin r × Fin r) ℤ)
    (hx : x ∈ nablaWt r ν μ) (hne : x ≠ 0) :
    (∀ k : ℕ, (∑ a : Fin r with a.val < k, μ a) ≤ ∑ a : Fin r with a.val < k, ν a) ∧ ∑ a, μ a = ∑ a, ν a := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hne
  have hdom := dualWeylDominanceZ r r ν le_rfl hν x hx.1 d hd
  have hwt : Finsupp.weight (rowW r r) d = μ := hx.2 (MvPolynomial.mem_support_iff.mp hd)
  have h1 : ∀ a, rowDeg d a = μ a := fun a => by rw [← ldrow_weight_rowW, hwt]
  have h2 : ∀ a : Fin r, rowNu (r := r) ν a = ν a := fun a => by
    unfold rowNu
    rw [dite_eq_left a.isLt]
  simpa only [h1, h2] using hdom

theorem exp_le_of_nonzero_weight_vectors (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) (hl : l.Prime)
    (H : ∀ x ∈ nablaWt r ν μ, x ≠ 0 → ExpLe l r ν μ e) : ExpLe l r ν μ e := by
  intro x hx
  by_cases h0 : x = 0
  · refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
    rw [h0, smul_zero]
    exact Submodule.zero_mem _
  · exact H x hx h0 x hx

theorem block_weight_last_antitone (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, w ≤ lam2 b) :
    Antitone (blockWtLast p q w lam2) := by
  intro a b
  unfold blockWtLast
  refine Fin.addCases (fun a' => ?_) (fun a' => ?_) a <;>
    refine Fin.addCases (fun b' => ?_) (fun b' => ?_) b <;> intro hab
  · rw [Fin.append_left, Fin.append_left]
    refine ha ?_
    have h1 : (Fin.castAdd p a').val ≤ (Fin.castAdd p b').val := hab
    simp only [Fin.val_castAdd] at h1
    exact Fin.le_def.mpr h1
  · rw [Fin.append_left, Fin.append_right]
    exact hb a'
  · exfalso
    have h1 : (Fin.natAdd q a').val ≤ (Fin.castAdd p b').val := hab
    have h2 := b'.isLt
    simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
    omega
  · rw [Fin.append_right, Fin.append_right]

theorem sum_lt_q_eq_sum_cast_add (p q : ℕ) (f : Fin (q + p) → ℕ) :
    (∑ a : Fin (q + p) with a.val < q, f a) = ∑ b : Fin q, f (Fin.castAdd p b) := by
  rw [Finset.sum_filter, Fin.sum_univ_add]
  simp

theorem depth_exists_last_block (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, w ≤ lam2 b)
    (μ : Fin (q + p) → ℕ) (x : MvPolynomial (Fin (q + p) × Fin (q + p)) ℤ)
    (hx : x ∈ nablaWt (q + p) (blockWtLast p q w lam2) μ) (hne : x ≠ 0) :
    ∃ i : ℕ, IsDepthLast p q w μ i ∧
      depth2 (fun a : Fin (q + p) => if a.val < q then 1 else 0) (blockWtLast p q w lam2) μ = (i : ℤ) := by
  obtain ⟨hdom, htot⟩ := dominance_of_nabla_weight _ _ μ (block_weight_last_antitone p q w lam2 ha hb) x hx hne
  have h1 := hdom q
  rw [sum_lt_q_eq_sum_cast_add, sum_lt_q_eq_sum_cast_add] at h1
  have h2 : ∀ b : Fin q, blockWtLast p q w lam2 (Fin.castAdd p b) = lam2 b := fun b => Fin.append_left _ _ b
  simp only [h2] at h1
  refine ⟨∑ b, lam2 b - ∑ b : Fin q, μ (Fin.castAdd p b), ?_⟩
  have hiff := depthLastIff p q w (∑ b, lam2 b - ∑ b : Fin q, μ (Fin.castAdd p b)) lam2 μ htot
  have h3 : depth2 (fun a : Fin (q + p) => if a.val < q then 1 else 0) (blockWtLast p q w lam2) μ =
      ((∑ b, lam2 b - ∑ b : Fin q, μ (Fin.castAdd p b) : ℕ) : ℤ) := by
    rw [depth_two_block_eq_sum_diff, Nat.cast_sub h1]
  exact ⟨hiff.mpr h3, h3⟩

theorem peelBoundLast : PeelBoundLast := by
  intro hD l q w M lam2 ξ hl ha hb hξ i' eL heL μ hμ
  have hl1 : 0 < l - 1 := by have := hl.two_le; omega
  refine exp_le_of_nonzero_weight_vectors l _ _ μ _ hl fun x hx hne => ?_
  obtain ⟨i, hd, _⟩ := depth_exists_last_block 1 q w lam2 ha (fun b => (hb b).1) μ x hx hne
  have h1 := hD l q w M lam2 ξ hl ha hb hξ i' eL heL i μ hd hμ
  refine expLeMono l _ _ μ _ _ ?_ h1
  refine Nat.add_le_add_left ?_ eL
  refine (Nat.le_div_iff_mul_le hl1).mpr ?_
  have h2 := dnVal l 1 (M - w) i q 0 (fun b : Fin q => M - lam2 (Fin.rev b)) hl fun b => by
    have := hb (Fin.rev b)
    exact ⟨Nat.zero_le _, by omega⟩
  rw [one_mul] at h2
  rw [mul_comm]
  refine le_trans h2 ?_
  rcases Nat.eq_zero_or_pos q with hq | hq
  · omega
  · have := hb ⟨0, hq⟩
    omega

theorem restriction_eq_block_weight (n t : ℕ) (lam : ℕ → ℕ) (hc : ∀ a, n ≤ a → a < n + t → lam a = lam n) :
    res (n + t) lam = blockWtLast t n (lam n) (res n lam) := by
  funext a
  unfold blockWtLast
  refine Fin.addCases (fun b => ?_) (fun b => ?_) a
  · rw [Fin.append_left]
    rfl
  · rw [Fin.append_right]
    show lam (Fin.natAdd n b).val = lam n
    rw [Fin.val_natAdd]
    exact hc _ (Nat.le_add_right _ _) (Nat.add_lt_add_left b.isLt n)

theorem restriction_antitone (n : ℕ) (lam : ℕ → ℕ) (ha : ∀ a b, a ≤ b → b < n → lam b ≤ lam a) : Antitone (res n lam) :=
  fun a b hab => ha a.val b.val hab b.isLt

theorem exponent_bound_peel_one_row (hD : BranchingBoundLastGradedOneRow) (l n : ℕ) (lam : ℕ → ℕ) (ξ : ℕ → ℤ) (hl : l.Prime)
    (ha : ∀ a b, a ≤ b → b < n + 1 → lam b ≤ lam a) (hξ : Antitone ξ) (I : ℤ) (e : ℕ)
    (hE : ExpUpTo l n lam ξ I e) : ExpUpTo l (n + 1) lam ξ I (e + (lam 0 + n - lam n - 1) / (l - 1)) := by
  intro μ hμ
  have hres := restriction_eq_block_weight n 1 lam (fun a h1 h2 => by
    have : a = n := by omega
    rw [this])
  rw [hres] at hμ ⊢
  refine peelBoundLast hD l n (lam n) (lam 0) (res n lam) (res (n + 1) ξ) hl
    (restriction_antitone n lam fun a b hab hb => ha a b hab (by omega))
    (fun b => ⟨ha b.val n (le_of_lt b.isLt) (by omega), ha 0 b.val (Nat.zero_le _) (by have := b.isLt; omega)⟩)
    (fun a b hab => hξ hab) I e (fun μ2 h2 => hE μ2 ?_) μ hμ
  rwa [depth2Levi] at h2

theorem peelRows : PeelRows := by
  intro hD l n s h lam ξ hl ha hh hξ I e hE
  induction s with
  | zero => simpa using hE
  | succ s ih =>
    have ih' := ih (fun a b hab hb => ha a b hab (by omega)) (by
      have := ha (n + s - 1) (n + s) (by omega) (by omega)
      have e1 : n + (s + 1) - 1 = n + s := by omega
      rw [e1] at hh
      omega)
    have h1 := exponent_bound_peel_one_row hD l (n + s) lam ξ hl (fun a b hab hb => ha a b hab (by omega)) hξ I _ ih'
    intro μ hμ
    refine expLeMono l _ _ μ _ _ ?_ (h1 μ hμ)
    have e1 : n + (s + 1) - 1 = n + s := by omega
    rw [e1] at hh
    have h2 : (lam 0 + (n + s) - lam (n + s) - 1) / (l - 1) ≤ (h - 1) / (l - 1) :=
      Nat.div_le_div_right (by omega)
    rw [Nat.succ_mul]
    omega

theorem blockStep : BlockStep := by
  intro hD l n t lam hl ht ha hc eL heL I μ hμ
  have hres := restriction_eq_block_weight n t lam hc
  have hanti : Antitone (res n lam) := restriction_antitone n lam fun a b hab hb => ha a b hab (by omega)
  have hb : ∀ b : Fin n, lam n ≤ res n lam b ∧ res n lam b ≤ lam 0 := fun b =>
    ⟨ha b.val n (le_of_lt b.isLt) (by omega), ha 0 b.val (Nat.zero_le _) (by have := b.isLt; omega)⟩
  rw [hres] at hμ ⊢
  refine exp_le_of_nonzero_weight_vectors l _ _ μ _ hl fun x hx hne => ?_
  obtain ⟨i, hd, hi⟩ := depth_exists_last_block t n (lam n) (res n lam) hanti (fun b => (hb b).1) μ x hx hne
  have hμ' : depth2 (fun a : Fin (n + t) => if a.val < n then 1 else 0) (blockWtLast t n (lam n) (res n lam)) μ ≤
      (I : ℤ) := hμ
  rw [hi] at hμ'
  have hiI : i ≤ I := by exact_mod_cast hμ'
  have h1 := hD l t n (lam n) (lam 0) (res n lam) hl hanti hb eL heL i μ hd
  refine expLeMono l _ _ μ _ _ (Nat.add_le_add_left ?_ eL) h1
  unfold blockCost
  exact Finset.le_sup (f := fun i => padicValInt l (Dn t (lam 0 - lam n) i fun b : Fin n => lam 0 - res n lam (Fin.rev b)))
    (Finset.mem_range.mpr (by omega))

theorem varpi_antitone (c : ℕ) : Antitone (varpi c) := by
  intro a b hab
  unfold varpi
  split_ifs <;> omega

theorem applicationSteps : ApplicationSteps := by
  intro hD l k j t q h lam hl ht ha hc hh ecl hecl I
  have hP1 := last_graded_implies_one_block' hD
  have hLast := lastGradedImpliesLast hD
  have s3 := peelRows hP1 l k j h lam (fun _ => 0) hl (fun a b hab hb => ha a b hab (by omega)) (by
      have := ha (k + j - 1) (k + j + t + q - 1) (by omega) (by omega)
      omega) (fun _ _ _ => le_rfl) 0 ecl (fun μ _ => hecl μ)
  have s3' : ∀ μ2 : Fin (k + j) → ℕ, ExpLe l (k + j) (res (k + j) lam) μ2 (ecl + j * ((h - 1) / (l - 1))) :=
    fun μ2 => s3 μ2 (by simp [depth2, res])
  have s2 := blockStep hLast l (k + j) t lam hl ht (fun a b hab hb => ha a b hab (by omega)) hc _ s3' I
  have s1 := peelRows hP1 l (k + j + t) q h lam (varpi (k + j)) hl ha hh (varpi_antitone _) I _ s2
  have e : q * ((h - 1) / (l - 1)) + blockCost l (k + j) t I lam + j * ((h - 1) / (l - 1)) + ecl =
      ecl + j * ((h - 1) / (l - 1)) + blockCost l (k + j) t I lam + q * ((h - 1) / (l - 1)) := by ring
  rwa [e]

end Formalism.CohomologicalDescent.LD
