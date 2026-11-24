module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import GroundTheory.GlobalFields.CompletionAtPlace.Galois
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.resDeg :
    CardRes → ResDeg := by
  intro hcard K M _ _ _ _ _ _ hn v w hns hunr _
  classical
  have hw : (w : HeightOneSpectrum (𝓞 M)).asIdeal.LiesOver v.asIdeal := w.2
  set f := (w : HeightOneSpectrum (𝓞 M)).asIdeal.inertiaDeg (𝓞 K)
  have hfconst : ∀ u : PlacesOver M v,
      (u : HeightOneSpectrum (𝓞 M)).asIdeal.inertiaDeg (𝓞 K) = f := by
    intro u
    haveI := u.2
    exact Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal _ _ Gal(M/K)
  have heone : ∀ u : PlacesOver M v,
      (u : HeightOneSpectrum (𝓞 M)).asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro u
    haveI := hunr u
    exact Ideal.ramificationIdx_eq_one _ _
  have hsum := GroundTheory.Global.SemiLocal.sum_ramificationIdx_mul_inertiaDeg M v
  have hdvd : f ∣ Module.finrank K M := by
    rw [← hsum]
    exact Finset.dvd_sum fun u _ => by rw [heone u, hfconst u, one_mul]
  have hf1 : f ≠ 1 := by
    intro h1
    refine hns fun u => ?_
    haveI := u.2
    have hrk := GroundTheory.Global.SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg M v
      (u : HeightOneSpectrum (𝓞 M))
    rw [heone u, hfconst u, h1, one_mul] at hrk
    exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hrk).2
  have hfn : f = Module.finrank K M := (hn.eq_one_or_self_of_dvd f hdvd).resolve_left hf1
  have hnormK : normV v = v.asIdeal.absNorm :=
    ((Ideal.absNorm_apply _).trans (Submodule.cardQuot_apply _)).symm
  have hnormM : normV (w : HeightOneSpectrum (𝓞 M)) =
      (w : HeightOneSpectrum (𝓞 M)).asIdeal.absNorm :=
    ((Ideal.absNorm_apply _).trans (Submodule.cardQuot_apply _)).symm
  have hpow : v.asIdeal.absNorm ^ f = (w : HeightOneSpectrum (𝓞 M)).asIdeal.absNorm :=
    Ideal.absNorm_pow_inertiaDeg v.asIdeal _
  have hK := hcard K v
  have hge : 2 ≤ v.asIdeal.absNorm := by
    have h0 := mt Ideal.absNorm_eq_zero_iff.1 v.ne_bot
    have h1 := mt Ideal.absNorm_eq_one_iff.1 v.isPrime.ne_top
    omega
  have hcardM : Nat.card 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] =
      Nat.card 𝓀[HeightOneSpectrum.adicCompletion K v] ^ Module.finrank K M := by
    rw [hcard M _, hK, hnormM, hnormK, ← hpow, hfn]
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion K v] :=
    Nat.finite_of_card_ne_zero (by rw [hK, hnormK]; omega)
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] :=
    Nat.finite_of_card_ne_zero (by rw [hcardM, hK, hnormK]; positivity)
  letI := Fintype.ofFinite 𝓀[HeightOneSpectrum.adicCompletion K v]
  refine ⟨?_, ?_⟩
  · have hc := Module.natCard_eq_pow_finrank (K := 𝓀[HeightOneSpectrum.adicCompletion K v])
      (V := 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))])
    rw [hcardM] at hc
    exact (Nat.pow_right_injective (by rwa [hK, hnormK]) hc).symm
  · refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic _ _, fun z => ?_⟩
    rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply, Nat.card_eq_fintype_card]
