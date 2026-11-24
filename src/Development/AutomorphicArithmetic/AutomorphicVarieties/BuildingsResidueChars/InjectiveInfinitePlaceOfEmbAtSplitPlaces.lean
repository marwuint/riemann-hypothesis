module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleEmbeddingExtension
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem mem_iff {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] {w : Plc L} (j : W.Emb l w) (x : 𝓞 L) :
    x ∈ w.asIdeal ↔ ‖j.1 (algebraMap L _ (x : L))‖ < 1 := by
  have h : w.asIdeal ≤ (GlobalTheory.EvExtend.placeOf (j.1.comp (algebraMap L _))).asIdeal := fun y hy => by
    rw [GlobalTheory.EvExtend.mem_placeOf]
    have h1 : Valued.v (algebraMap L (w.adicCompletion L) (y : L)) < 1 := by
      rw [ReciprocityTheory.Aut.adic_valued_algebraMap]
      exact (w.valuation_lt_one_iff_mem (K := L) y).2 hy
    have h2 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one h1)
    rw [map_zero] at h2
    exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (h2.congr fun n => map_pow j.1 _ n)
  rw [w.isMaximal.eq_of_le (GlobalTheory.EvExtend.placeOf _).isPrime.ne_top h, GlobalTheory.EvExtend.mem_placeOf]
  rfl

private theorem not_stable {L : Type} [Field L] [NumberField L] [IsCMField L] {w : Plc L} (hw : IsSplitAt w)
    (h : ∀ x, IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal → x ∈ w.asIdeal) : False := by
  obtain ⟨u, hu, hu'⟩ := hw
  refine hu (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top fun x hx => ?_))
  obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff L (x * IsCMField.ringOfIntegersComplexConj L x)).1 (by
    rw [map_mul, mul_comm]
    congr 1
    exact RingOfIntegers.ext (IsCMField.complexConj_apply_apply L x))
  have h1 : y ∈ (u.under (𝓞 (Lp L))).asIdeal := by
    change algebraMap _ (𝓞 L) y ∈ u.asIdeal
    rw [hy]
    exact Ideal.mul_mem_right _ _ hx
  rw [hu'] at h1
  change algebraMap _ (𝓞 L) y ∈ w.asIdeal at h1
  rw [hy] at h1
  exact (w.isPrime.mem_or_mem h1).elim id (h x)

theorem UpperTheory.injective_infinitePlace_of_emb_at_split_places :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V : s.Lev) (ι : Qbar l ≃+* ℂ), Function.Injective fun y : Emb l (fun v : V.frame.Vl => s.w v.1) => InfinitePlace.mk (ι.toRingHom.comp y.res) := by
  intro l _ L Ω _ _ _ _ _ _ s V ι
  rintro ⟨v, j⟩ ⟨v', j'⟩ h
  have h' : (∀ x : L, j.1 (algebraMap L _ x) = j'.1 (algebraMap L _ x)) ∨
      ∀ x : L, j.1 (algebraMap L _ (IsCMField.complexConj L x)) = j'.1 (algebraMap L _ x) := by
    refine (InfinitePlace.mk_eq_iff.1 h).imp (fun e x => ι.injective (RingHom.congr_fun e x)) fun e x => ι.injective ?_
    exact (IsCMField.complexEmbedding_complexConj L (ι.toRingHom.comp (j.1.comp (algebraMap L _))) x).trans
      (RingHom.congr_fun e x)
  have hv : v = v' := by
    apply Subtype.ext
    rw [← w_under s v.1, ← w_under s v'.1]
    ext x
    change algebraMap _ (𝓞 L) x ∈ (s.w v.1).asIdeal ↔ algebraMap _ (𝓞 L) x ∈ (s.w v'.1).asIdeal
    rw [mem_iff j, mem_iff j']
    rcases h' with e | e
    · rw [e]
    · rw [← e]
      have : IsCMField.complexConj L ((algebraMap _ (𝓞 L) x : 𝓞 L) : L) = ((algebraMap _ (𝓞 L) x : 𝓞 L) : L) :=
        IsCMField.complexConj_apply_eq_self L (x : Lp L)
      rw [this]
  subst hv
  rcases h' with e | e
  · have : j = j' := Subtype.ext (DFunLike.coe_injective
      ((HeightOneSpectrum.denseRange_algebraMap L (s.w v.1)).equalizer j.2 j'.2 (funext e)))
    rw [this]
  · refine (not_stable (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A v.1) v.1 (s.hA _) (s.split _ (Or.inl v.2)) _ (w_under s _)) fun x hx => ?_).elim
    rw [mem_iff j] at hx
    rwa [mem_iff j', ← e]
