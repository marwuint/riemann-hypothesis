module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.UnitaryGroupMassFormula.RLRS

namespace IsRegularLocalRing

open IsLocalRing RingTheory.Sequence

open scoped Pointwise

universe u

theorem isWeaklyRegular_cons_of_quotient {A : Type u} [CommRing A] {x : A}
    (hx : IsSMulRegular A x) (ys : List A)
    (hys : IsWeaklyRegular (A ⧸ Ideal.span ({x} : Set A))
      (ys.map (Ideal.Quotient.mk (Ideal.span ({x} : Set A))))) :
    IsWeaklyRegular A (x :: ys) := by
  rw [isWeaklyRegular_cons_iff]
  refine ⟨hx, ?_⟩
  have h : (x • ⊤ : Submodule A A) = Ideal.span ({x} : Set A) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  have e : QuotSMulTop x A ≃ₗ[A] A ⧸ Ideal.span ({x} : Set A) :=
    Submodule.quotEquivOfEq _ _ h
  rw [e.isWeaklyRegular_congr]
  refine (isWeaklyRegular_map_algebraMap_iff (A ⧸ Ideal.span ({x} : Set A))
    (A ⧸ Ideal.span ({x} : Set A)) ys).mp ?_
  rwa [Ideal.Quotient.algebraMap_eq]

theorem exists_list_of_spanFinrank_eq :
    ∀ (n : ℕ) (A : Type u) [CommRing A] [IsRegularLocalRing A],
      Submodule.spanFinrank (maximalIdeal A) = n →
      ∃ xs : List A, Ideal.ofList xs = maximalIdeal A ∧ xs.length = n ∧
        IsWeaklyRegular A xs := by
  intro n
  induction n with
  | zero =>
    intro A _ _ h
    refine ⟨[], ?_, rfl, IsWeaklyRegular.nil A A⟩
    rw [Ideal.ofList_nil]
    exact ((Submodule.spanFinrank_eq_zero_iff_eq_bot
      (IsNoetherian.noetherian (maximalIdeal A))).mp h).symm
  | succ n IH =>
    intro A _ _ h
    have hsq : ¬ maximalIdeal A ≤ maximalIdeal A ^ 2 := by
      intro hle
      have hbot := maximalIdeal_eq_bot_of_le_sq A hle
      rw [hbot, Submodule.spanFinrank_bot] at h
      omega
    obtain ⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal A ∧ x ∉ maximalIdeal A ^ 2 := by
      by_contra hc
      push Not at hc
      exact hsq fun y hy => hc y hy
    have hreg : IsRegularLocalRing (A ⧸ Ideal.span ({x} : Set A)) :=
      quotient_span_singleton hx hx2
    have hdim := spanFinrank_quotient_eq_and_ringKrullDim_add_one A hx hx2
    have hn : Submodule.spanFinrank (maximalIdeal (A ⧸ Ideal.span ({x} : Set A))) = n := by
      have h3 : ((Submodule.spanFinrank (maximalIdeal A) : ℕ) : WithBot ℕ∞) = ringKrullDim A :=
        _root_.IsRegularLocalRing.spanFinrank_maximalIdeal
      have h2 := hdim.2
      rw [← hdim.1, ← h3, h] at h2
      have h4 : Submodule.spanFinrank (maximalIdeal (A ⧸ Ideal.span ({x} : Set A))) + 1
          = n + 1 := by exact_mod_cast h2
      omega
    obtain ⟨ys', hys'1, hys'2, hys'3⟩ := IH (A ⧸ Ideal.span ({x} : Set A)) hn
    have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span ({x} : Set A))) :=
      Ideal.Quotient.mk_surjective
    have hmap : (ys'.map (Function.surjInv hsurj)).map
        (Ideal.Quotient.mk (Ideal.span ({x} : Set A))) = ys' := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id ys']
      exact List.map_congr_left (fun a _ => Function.surjInv_eq hsurj a)
    generalize hL : ys'.map (Function.surjInv hsurj) = L at hmap
    have hcomap : Ideal.comap (Ideal.Quotient.mk (Ideal.span ({x} : Set A)))
        (maximalIdeal (A ⧸ Ideal.span ({x} : Set A))) = maximalIdeal A := by
      have hmax := Ideal.comap_isMaximal_of_surjective
        (Ideal.Quotient.mk (Ideal.span ({x} : Set A))) hsurj
        (K := maximalIdeal (A ⧸ Ideal.span ({x} : Set A)))
      exact IsLocalRing.eq_maximalIdeal hmax
    have hofl : Ideal.ofList (x :: L) = maximalIdeal A := by
      rw [← hcomap, ← hys'1, ← hmap, ← Ideal.map_ofList,
        Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        Ideal.ofList_cons, sup_comm]
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx2 (zero_mem _)
    have hxreg : IsSMulRegular A x := fun a b hab => mul_left_cancel₀ hx0 hab
    refine ⟨x :: L, hofl, by rw [← hL]; simp [hys'2], ?_⟩
    refine isWeaklyRegular_cons_of_quotient hxreg _ ?_
    rwa [hmap]

theorem exists_isRegular_ofList_eq_maximalIdeal (A : Type u) [CommRing A]
    [IsRegularLocalRing A] :
    ∃ xs : List A, Ideal.ofList xs = maximalIdeal A ∧
      (xs.length : WithBot ℕ∞) = ringKrullDim A ∧ IsRegular A xs := by
  obtain ⟨xs, h1, h2, h3⟩ := exists_list_of_spanFinrank_eq _ A rfl
  refine ⟨xs, h1, ?_, ?_⟩
  · rw [h2]
    exact _root_.IsRegularLocalRing.spanFinrank_maximalIdeal
  · refine RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A ?_ h3
    intro r hr
    rw [← h1]
    exact Ideal.subset_span hr

end IsRegularLocalRing

end PI.UnitaryGroupMassFormula.RLRS
