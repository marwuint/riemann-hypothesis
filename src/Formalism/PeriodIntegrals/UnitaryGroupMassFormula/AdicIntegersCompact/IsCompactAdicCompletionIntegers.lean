module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
public import Formalism.LocalToGlobal.AdelicCompactOpens.IntAdelesCompactOpen
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.IntAdCpctOpenWork

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isOpen_lt_one (x : v.adicCompletion F) :
    IsOpen {y : v.adicCompletion F | Valued.v (y - x) < 1} := by
  have h1 : IsOpen {z : v.adicCompletion F | Valued.v z < 1} := by
    have := Valued.isOpen_ball (v.adicCompletion F) 1
    simpa only [Valuation.restrict_lt_one_iff] using this
  exact h1.preimage (continuous_id.sub continuous_const)

theorem valued_algebraMap (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem denseRange : DenseRange (algebraMap F (v.adicCompletion F)) := denseRange_algebraMap F v

theorem exists_close (x : v.adicCompletion F) (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
  apply PI.WAU.exists_int_near <;> assumption

theorem mem_maximalIdeal_iff (x : Valued.integer (v.adicCompletion F)) :
    x ∈ IsLocalRing.maximalIdeal (Valued.integer (v.adicCompletion F)) ↔
      Valued.v (x : v.adicCompletion F) < 1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one

noncomputable def toInt : 𝓞 F →+* Valued.integer (v.adicCompletion F) :=
  ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict
    (Valued.integer (v.adicCompletion F)) (fun a => by
      show Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) ≤ 1
      rw [valued_algebraMap]
      exact valuation_le_one v a)

noncomputable def resHom :
    𝓞 F →+* IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F)) :=
  (IsLocalRing.residue _).comp (toInt v)

theorem resHom_surjective : Function.Surjective (resHom v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := exists_close v x x.2
  refine ⟨a, ?_⟩
  unfold resHom
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]
  have e : ((toInt v a - x : Valued.integer (v.adicCompletion F)) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) - x := rfl
  rwa [e, Valuation.map_sub_swap]

theorem resHom_eq_zero (a : 𝓞 F) (ha : a ∈ v.asIdeal) : resHom v a = 0 := by
  unfold resHom
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]
  show Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1
  rw [valued_algebraMap]
  exact (valuation_lt_one_iff_mem v a).mpr ha

theorem finite_residueField : Finite (Valued.ResidueField (v.adicCompletion F)) := by
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let g := Ideal.Quotient.lift v.asIdeal (resHom v) (fun a ha => resHom_eq_zero v a ha)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := resHom_surjective v y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  exact Finite.of_surjective g hg

theorem compactSpace_integer : CompactSpace (Valued.integer (v.adicCompletion F)) := by
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  refine ⟨?_, ?_, finite_residueField v⟩
  · exact ((Valued.v.integer.toAddSubgroup).isClosed_of_isOpen (Valued.isOpen_integer _)).completeSpace_coe
  · exact (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F))

theorem isCompact_adicCompletionIntegers :
    IsCompact ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  haveI := compactSpace_integer v
  exact isCompact_iff_compactSpace.mpr this

instance compactSpace_set : CompactSpace ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers v)

instance compactSpace_sub : CompactSpace (v.adicCompletionIntegers F) :=
  isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers v)

theorem main : Formalism.L2.Props.IntAdelesCompactOpen := by
  intro F _ _
  have hO : ∀ w : HeightOneSpectrum (𝓞 F),
      IsOpen ((w.adicCompletionIntegers F : Set (w.adicCompletion F))) :=
    fun w => Valued.isOpen_valuationSubring _
  refine ⟨RestrictedProduct.isOpen_forall_mem hO, ?_⟩
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap hO).continuous
  rwa [RestrictedProduct.range_structureMap] at h

end PI.IntAdCpctOpenWork
