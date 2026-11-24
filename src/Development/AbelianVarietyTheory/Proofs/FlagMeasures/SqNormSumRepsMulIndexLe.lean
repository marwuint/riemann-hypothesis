module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate

namespace GlobalTheory.HL.GaussSum

theorem sq_norm_sum_mul_index_le {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G)
    (f : G → ℂ) (hf : ∀ u, ‖f u‖ = 1)
    (hQ : ∀ h, h ∉ Q → ∃ (v : G) (c : ℂ), c ≠ 1 ∧
      ∀ u, f (u + v + h) * conj (f (u + v)) = c * (f (u + h) * conj (f u))) :
    ‖∑ u, f u‖ ^ 2 * (Q.index : ℝ) ≤ (Fintype.card G : ℝ) ^ 2 := by
  classical
  have hzero : ∀ h, h ∉ Q → ∑ u, f (u + h) * conj (f u) = 0 := by
    intro h hh
    obtain ⟨v, c, hc, hrel⟩ := hQ h hh
    have h1 : ∑ u, f (u + h) * conj (f u) = c * ∑ u, f (u + h) * conj (f u) := by
      rw [Finset.mul_sum]
      calc ∑ u, f (u + h) * conj (f u) = ∑ u, f (u + v + h) * conj (f (u + v)) :=
            (Fintype.sum_equiv (Equiv.addRight v) (fun u => f (u + v + h) * conj (f (u + v)))
              (fun u => f (u + h) * conj (f u)) (fun u => rfl)).symm
        _ = ∑ u, c * (f (u + h) * conj (f u)) := Finset.sum_congr rfl fun u _ => hrel u
    have h2 : (1 - c) * ∑ u, f (u + h) * conj (f u) = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3).symm hc
    · exact h3
  have hexp : (∑ u, f u) * conj (∑ u, f u) = ∑ h, ∑ u, f (u + h) * conj (f u) := by
    calc (∑ u, f u) * conj (∑ u, f u) = ∑ w, ∑ u, f w * conj (f u) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.sum_mul_sum]
      _ = ∑ u, ∑ w, f w * conj (f u) := Finset.sum_comm
      _ = ∑ u, ∑ h, f (u + h) * conj (f u) := Finset.sum_congr rfl fun u _ =>
          (Fintype.sum_equiv (Equiv.addLeft u) (fun h => f (u + h) * conj (f u))
            (fun w => f w * conj (f u)) (fun h => rfl)).symm
      _ = ∑ h, ∑ u, f (u + h) * conj (f u) := Finset.sum_comm
  have hnorm : ‖∑ u, f u‖ ^ 2 ≤ (Fintype.card G : ℝ) * (Nat.card Q : ℝ) := by
    calc ‖∑ u, f u‖ ^ 2 = ‖(∑ u, f u) * conj (∑ u, f u)‖ := by
          rw [norm_mul, RCLike.norm_conj, sq]
      _ = ‖∑ h, ∑ u, f (u + h) * conj (f u)‖ := by rw [hexp]
      _ ≤ ∑ h, ‖∑ u, f (u + h) * conj (f u)‖ := norm_sum_le _ _
      _ ≤ ∑ h, (if h ∈ Q then (Fintype.card G : ℝ) else 0) := by
          refine Finset.sum_le_sum fun h _ => ?_
          split_ifs with hh
          · calc ‖∑ u, f (u + h) * conj (f u)‖ ≤ ∑ u, ‖f (u + h) * conj (f u)‖ :=
                  norm_sum_le _ _
              _ = ∑ _u : G, (1 : ℝ) := by simp [hf]
              _ = Fintype.card G := by simp
          · rw [hzero h hh, norm_zero]
      _ = (Fintype.card G : ℝ) * (Nat.card Q : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_comm]
          congr 1
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hci : (Nat.card Q : ℝ) * (Q.index : ℝ) = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, ← AddSubgroup.card_mul_index (H := Q)]
    push_cast
    ring
  calc ‖∑ u, f u‖ ^ 2 * (Q.index : ℝ) ≤ (Fintype.card G : ℝ) * Nat.card Q * Q.index :=
        mul_le_mul_of_nonneg_right hnorm (Nat.cast_nonneg _)
    _ = (Fintype.card G : ℝ) ^ 2 := by rw [mul_assoc, hci, sq]

theorem sq_norm_sum_reps_mul_index_le {M : Type*} [AddCommGroup M] (P Q : AddSubgroup M)
    (hPQ : P ≤ Q) (R : Finset M) (hR : ∀ u, ∃! w, w ∈ R ∧ u - w ∈ P)
    (f : M → ℂ) (hf : ∀ u, ‖f u‖ = 1) (hP : ∀ u, ∀ p ∈ P, f (u + p) = f u)
    (hQ : ∀ h, h ∉ Q → ∃ (v : M) (c : ℂ), c ≠ 1 ∧
      ∀ u, f (u + v + h) * conj (f (u + v)) = c * (f (u + h) * conj (f u))) :
    ‖∑ u ∈ R, f u‖ ^ 2 * (Q.index : ℝ) ≤ (R.card : ℝ) ^ 2 := by
  classical
  have hsurj : ∀ x : M ⧸ P, ∃ w ∈ R, (w : M ⧸ P) = x := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨w, ⟨hwR, hw⟩, -⟩ := hR u
    refine ⟨w, hwR, ?_⟩
    rw [QuotientAddGroup.eq]
    have e : -w + u = u - w := by abel
    rwa [e]
  have hinj : ∀ w ∈ R, ∀ w' ∈ R, (w : M ⧸ P) = w' → w = w' := by
    intro w hw w' hw' h
    rw [QuotientAddGroup.eq] at h
    obtain ⟨z, -, hz⟩ := hR w
    have h1 : w = z := hz w ⟨hw, by simp⟩
    have h2 : w' = z := hz w' ⟨hw', by
      rw [show w - w' = -(-w + w') by abel]
      exact P.neg_mem h⟩
    rw [h1, h2]
  have : Finite (M ⧸ P) := by
    apply Finite.of_surjective (fun w : R => ((w : M) : M ⧸ P))
    intro x
    obtain ⟨w, hw, rfl⟩ := hsurj x
    exact ⟨⟨w, hw⟩, rfl⟩
  let : Fintype (M ⧸ P) := Fintype.ofFinite _
  have hf' : ∀ u : M, f ((u : M ⧸ P)).out = f u := by
    intro u
    have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (u : M ⧸ P))
    have e := hP ((u : M ⧸ P)).out _ h
    rw [add_neg_cancel_left] at e
    exact e.symm
  have h1 := GlobalTheory.HL.GaussSum.sq_norm_sum_mul_index_le (Q.map (QuotientAddGroup.mk' P))
    (fun x : M ⧸ P => f x.out) (fun x => hf _) (by
      intro h' hh'
      obtain ⟨h, rfl⟩ := QuotientAddGroup.mk_surjective h'
      have hhQ : h ∉ Q := fun hq => hh' (AddSubgroup.mem_map_of_mem _ hq)
      obtain ⟨v, c, hc, hrel⟩ := hQ h hhQ
      refine ⟨(v : M ⧸ P), c, hc, fun x => ?_⟩
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
      simp only [← QuotientAddGroup.mk_add, hf']
      exact hrel u)
  have hidx : (Q.map (QuotientAddGroup.mk' P)).index = Q.index :=
    AddSubgroup.index_map_eq (H := Q) (QuotientAddGroup.mk'_surjective P)
      (by rw [QuotientAddGroup.ker_mk']; exact hPQ)
  have hi1 : ∀ a ∈ R, ((a : M ⧸ P)) ∈ (Finset.univ : Finset (M ⧸ P)) :=
    fun _ _ => Finset.mem_univ _
  have hi2 : Set.InjOn (fun a : M => (a : M ⧸ P)) R := fun w hw w' hw' h => hinj w hw w' hw' h
  have hi3 : Set.SurjOn (fun a : M => (a : M ⧸ P)) R (↑(Finset.univ : Finset (M ⧸ P)) : Set (M ⧸ P)) := by
    intro x _
    obtain ⟨w, hw, rfl⟩ := hsurj x
    exact ⟨w, hw, rfl⟩
  have hsum : ∑ u ∈ R, f u = ∑ x : M ⧸ P, f x.out :=
    Finset.sum_nbij (fun a : M => (a : M ⧸ P)) hi1 hi2 hi3 (fun u _ => (hf' u).symm)
  have hcard : R.card = Fintype.card (M ⧸ P) := by
    rw [← Finset.card_univ]
    exact Finset.card_nbij (fun a : M => (a : M ⧸ P)) hi1 hi2 hi3
  rwa [hsum, hcard, ← hidx]

theorem mul_conj_eq {A : Type*} [AddCommGroup A] (ψ : AddChar A ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x y : A) :
    ψ x * conj (ψ y) = ψ (x - y) := by
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, Complex.inv_def,
    Complex.normSq_eq_norm_sq, h y]
  simp

end GlobalTheory.HL.GaussSum
