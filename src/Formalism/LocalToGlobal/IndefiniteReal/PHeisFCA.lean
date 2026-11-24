module

public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CompactFixesLattice
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory IsDedekindDomain NumberField Topology
open scoped RestrictedProduct Classical

namespace Formalism.IndefR.PHeisFC

variable (F : Type) [Field F] [NumberField F]

abbrev eM : InfiniteAdeleRing F ≃+* mixedEmbedding.mixedSpace F := InfiniteAdeleRing.ringEquiv_mixedSpace F

theorem eM_apply (x : InfiniteAdeleRing F) :
    eM F x = ((fun v : {w : InfinitePlace F // w.IsReal} =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1)),
      fun v : {w : InfinitePlace F // w.IsComplex} => InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)) :=
  InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x

def Pinf : Set (InfiniteAdeleRing F) := eM F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

theorem eM_algebraMap (a : F) : eM F (algebraMap F (InfiniteAdeleRing F) a) = mixedEmbedding F a := by
  first
  | exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm

theorem inf_exU (x : InfiniteAdeleRing F) : ∃! a : 𝓞 F, algebraMap F (InfiniteAdeleRing F) (a : F) + x ∈ Pinf F := by
  have key : ∀ a : 𝓞 F, (algebraMap F (InfiniteAdeleRing F) (a : F) + x ∈ Pinf F) ↔
      mixedEmbedding F (a : F) + eM F x ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) := by
    intro a
    show eM F (algebraMap F (InfiniteAdeleRing F) (a : F) + x) ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) ↔ _
    rw [map_add (f := _), eM_algebraMap]
  have hmem : ∀ a : 𝓞 F, mixedEmbedding F (a : F) ∈
      Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) := by
    intro a
    rw [mixedEmbedding.mem_span_latticeBasis]
    exact ⟨a, rfl⟩
  obtain ⟨v, hv, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (mixedEmbedding.latticeBasis F) (eM F x)
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 F, mixedEmbedding F (a : F) = (v : mixedEmbedding.mixedSpace F) := by
    have hv2 := v.2
    rw [mixedEmbedding.mem_span_latticeBasis] at hv2
    obtain ⟨a, ha⟩ := hv2
    exact ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩
  · show algebraMap F (InfiniteAdeleRing F) (a : F) + x ∈ Pinf F
    rw [key, ha]
    simpa [Submodule.vadd_def] using hv
  · intro b hb0
    have hb : algebraMap F (InfiniteAdeleRing F) (b : F) + x ∈ Pinf F := hb0
    rw [key] at hb
    have h1 : (⟨mixedEmbedding F (b : F), hmem b⟩ :
        Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F))) = v := by
      apply hu
      simpa [Submodule.vadd_def] using hb
    have h2 : mixedEmbedding F (b : F) = mixedEmbedding F (a : F) := by
      rw [ha]
      exact congrArg Subtype.val h1
    have h3 : (b : F) = (a : F) := mixedEmbedding_injective F h2
    first | exact RingOfIntegers.ext h3

theorem measurableSet_Pinf : MeasurableSet (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem Pinf_sub_compact : ∃ K : Set (InfiniteAdeleRing F), IsCompact K ∧ Pinf F ⊆ K := by
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis F)).subset_closedBall 0
  refine ⟨Set.pi Set.univ (fun w => (InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 R),
    ?_, ?_⟩
  · refine isCompact_univ_pi fun w => ?_
    have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
    first
    | exact hi.isClosedEmbedding.isCompact_preimage (isCompact_closedBall 0 R)
  · intro x hx
    have hx' : ‖eM F x‖ ≤ R := mem_closedBall_zero_iff.mp (hR (show eM F x ∈ _ from hx))
    show ∀ w ∈ (Set.univ : Set (InfinitePlace F)),
      x w ∈ (InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 R
    intro w _
    have hn : ‖InfinitePlace.Completion.extensionEmbedding w (x w)‖ = ‖x w‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (x w)
    show InfinitePlace.Completion.extensionEmbedding w (x w) ∈ Metric.closedBall 0 R
    rw [mem_closedBall_zero_iff, hn]
    by_cases hw : w.IsReal
    · have hr : ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x w)‖ = ‖x w‖ :=
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) (x w)
      have e : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x w) = (eM F x).1 ⟨w, hw⟩ := by
        rw [eM_apply]
      rw [← hr, e]
      exact ((norm_le_pi_norm _ _).trans (norm_fst_le _)).trans hx'
    · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have e : InfinitePlace.Completion.extensionEmbedding w (x w) = (eM F x).2 ⟨w, hc⟩ := by
        rw [eM_apply]
      rw [← hn, e]
      exact ((norm_le_pi_norm _ _).trans (norm_snd_le _)).trans hx'

abbrev Ohat : Set (FiniteAdeleRing (𝓞 F) F) := (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F : Set (FiniteAdeleRing (𝓞 F) F))

theorem isOpen_Ohat : IsOpen (Ohat F) := by
  first | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.isOpen_intAd

theorem isCompact_Ohat : IsCompact (Ohat F) := Formalism.L2.Col.rlt_isCompact_intAd

def F0 : Set (AdeleRing (𝓞 F) F) := {x | x.1 ∈ Pinf F ∧ x.2 ∈ Ohat F}

theorem ad_exU (x : AdeleRing (𝓞 F) F) : ∃! q : F, algebraMap F (AdeleRing (𝓞 F) F) q + x ∈ F0 F := by
  have hOa : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := by
    intro a v
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (a : F)).trans_le
      (HeightOneSpectrum.valuation_le_one v a)
  have hint : ∀ q : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) q ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F →
      ∃ a : 𝓞 F, (a : F) = q := by
    intro q hq
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) q
      fun v => (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q).symm.trans_le (hq v)
    exact ⟨a, ha⟩
  obtain ⟨u, hu⟩ : ∃ u : F, x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) u ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨a, ha, hauniq⟩ := inf_exU F (algebraMap F (InfiniteAdeleRing F) (-u) + x.1)
  refine ⟨-u + (a : F), ?_, ?_⟩
  · simp only [F0, Set.mem_setOf_eq]
    constructor
    · change algebraMap F (InfiniteAdeleRing F) (-u + (a : F)) + x.1 ∈ Pinf F
      convert ha using 1
      rw [map_add (f := _)]
      abel
    · change algebraMap F (FiniteAdeleRing (𝓞 F) F) (-u + (a : F)) + x.2 ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F
      convert add_mem hu (hOa a) using 1
      rw [map_add (f := _), map_neg]
      abel
  · intro q hq
    obtain ⟨h1, h2⟩ := hq
    have h2' : algebraMap F (FiniteAdeleRing (𝓞 F) F) q + x.2 ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := h2
    have h1' : algebraMap F (InfiniteAdeleRing F) q + x.1 ∈ Pinf F := h1
    have h3 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (q + u) ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := by
      convert sub_mem h2' hu using 1
      rw [map_add (f := _)]
      abel
    obtain ⟨b, hb⟩ := hint (q + u) h3
    have h5 : algebraMap F (InfiniteAdeleRing F) (b : F) + (algebraMap F (InfiniteAdeleRing F) (-u) + x.1) ∈ Pinf F := by
      convert h1' using 1
      rw [hb, map_add (f := _), map_neg]
      abel
    rw [hauniq b h5] at hb
    rw [hb]; ring

theorem fundamental_set_subset_compact : ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ F0 F ⊆ K := by
  obtain ⟨K1, hK1, hsub⟩ := Pinf_sub_compact F
  refine ⟨K1 ×ˢ Ohat F, hK1.prod (isCompact_Ohat F), ?_⟩
  intro x hx
  simp only [F0, Set.mem_setOf_eq] at hx
  exact ⟨hsub hx.1, hx.2⟩

instance instT2SpaceFiniteAdeles : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ (v : HeightOneSpectrum (𝓞 F)), [v.adicCompletion F, v.adicCompletionIntegers F]))

instance t2Space_numberFieldInfiniteAdeles : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

instance t2AF : T2Space (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

instance wlcAfin : WeaklyLocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) where
  exists_compact_mem_nhds x := by
    refine ⟨(fun y => x + y) '' Ohat F, (isCompact_Ohat F).image (continuous_const.add continuous_id), ?_⟩
    have ho : IsOpen ((fun y => y - x) ⁻¹' Ohat F) := (isOpen_Ohat F).preimage (continuous_id.sub continuous_const)
    refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
    · show x - x ∈ Ohat F
      rw [sub_self]; exact zero_mem (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F)
    · intro y hy
      exact ⟨y - x, hy, by simp⟩

instance lcAfin : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := WeaklyLocallyCompactSpace.locallyCompactSpace

instance lcAF : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end Formalism.IndefR.PHeisFC

end
