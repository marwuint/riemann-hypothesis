module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pl_sub :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (H K : Subgroup Γ) [H.Normal] [K.Normal], IsOpen (K : Set Γ) → H ≤ K → ∀ U : OpenNormalSubgroup K, (∀ h : K, (h : Γ) ∈ H → ∃ e : ℕ, h ^ l ^ e ∈ U) → ∀ g : K, (g : Γ) ∈ PL (l := l) H → g ∈ U := by
  intro l _ Γ _ _ _ _ _ H K _ _ hK hHK U hU g hg
  have hl : l.Prime := Fact.out
  have hKc : IsClosed (K : Set Γ) := OpenSubgroup.isClosed ⟨K, hK⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc.isCompact
  haveI : U.toSubgroup.FiniteIndex := U.toOpenSubgroup.toSubgroup.finiteIndex_of_finite_quotient
  haveI : U.toSubgroup.Normal := U.isNormal'
  have hn0 : U.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have lem : ∀ k : K, (k : Γ) ∈ H → k ^ l ^ U.toSubgroup.index ∈ U.toSubgroup := by
    intro k hk
    obtain ⟨e, he⟩ := hU k hk
    set q : K ⧸ U.toSubgroup := (QuotientGroup.mk k : K ⧸ U.toSubgroup)
    have hqe : q ^ l ^ e = 1 := by
      rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have hqn : q ^ U.toSubgroup.index = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact U.toSubgroup.pow_index_mem k
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hqe)
    have h1 : l ^ a ≤ U.toSubgroup.index := by
      rw [← ha]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (orderOf_dvd_of_pow_eq_one hqn)
    have h2 : a < l ^ a := Nat.lt_pow_self hl.one_lt
    have h3 : orderOf q ∣ l ^ U.toSubgroup.index := by
      rw [ha]
      exact pow_dvd_pow l (by omega)
    have hq : q ^ l ^ U.toSubgroup.index = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hq
  let O : Subgroup Γ := U.toSubgroup.map K.subtype
  have hOo : IsOpen (O : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hK.isOpenMap_subtype_val _ U.toOpenSubgroup.isOpen
  have hOc : IsClosed (O : Set Γ) := OpenSubgroup.isClosed ⟨O, hOo⟩
  haveI : Finite (Γ ⧸ O) := O.quotient_finite_of_isOpen hOo
  haveI : O.FiniteIndex := O.finiteIndex_of_finite_quotient
  have hCo : IsOpen (O.normalCore : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (O.normalCore_isClosed hOc)
  let C : OpenNormalSubgroup Γ :=
    { toOpenSubgroup := ⟨O.normalCore, hCo⟩
      isNormal' := O.normalCore_normal }
  have hcond : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ C.toOpenSubgroup := by
    intro h hh
    refine ⟨U.toSubgroup.index, ?_⟩
    show ∀ b : Γ, b * h ^ l ^ U.toSubgroup.index * b⁻¹ ∈ O
    intro b
    rw [← conj_pow]
    have hbH : b * h * b⁻¹ ∈ H := ‹H.Normal›.conj_mem h hh b
    exact Subgroup.mem_map.mpr ⟨_, (lem ⟨b * h * b⁻¹, hHK hbH⟩ hbH), rfl⟩
  have hgC : (g : Γ) ∈ C.toOpenSubgroup := by
    unfold PL at hg
    exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hg C) hcond
  have hgO : (g : Γ) ∈ O := O.normalCore_le hgC
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgO
  have : x = g := Subtype.ext hxg
  rwa [← this]
