import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinOrdLeOrdAdd
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocModelLocRingAndExistsTrBasis

set_option autoImplicit false

noncomputable section

open GlobalTheory.TopForm

namespace GlobalTheory.FieldPair.AdjModel

variable {k K : Type} [Field k] [Field K] {c : k →+* K} {n : ℕ}

theorem exists_place {Q : Subring K} (hQ : IsLocModel c Q) {t : Q} (ht : Prime t) :
    ∃ S : Place c, S.IsPrimeOf Q ∧ S.ord (t : K) = 1 ∧
      ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ord (t : K) = 0 := by
  let c0 := c.codRestrict Q hQ.const_mem
  haveI : IsNoetherianRing Q := by
    letI := c0.toAlgebra
    haveI : Algebra.EssFiniteType k Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing k Q
  haveI : IsFractionRing Q K := by
    refine IsFractionRing.of_field Q K fun z => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hQ.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩
  let p : Ideal Q := Ideal.span {t}
  haveI : p.IsPrime := (Ideal.span_singleton_prime ht.ne_zero).2 ht
  have hp : p.primeCompl ≤ nonZeroDivisors Q := p.primeCompl_le_nonZeroDivisors
  let A : Subalgebra Q K := Localization.subalgebra.ofField K p.primeCompl hp
  haveI hA : IsLocalization p.primeCompl A := Localization.subalgebra.isLocalization_ofField K _ hp
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A p
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap Q A t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A, Ideal.map_span, Set.image_singleton]
  have ht0 : algebraMap Q A t ≠ 0 := fun e => ht.ne_zero (Subtype.ext (congrArg (fun z : A => (z : K)) e))
  have hnf : ¬ IsField A := fun hf => ht0 (by
    have := IsLocalRing.isField_iff_maximalIdeal_eq.1 hf
    rw [hm] at this
    exact Ideal.span_singleton_eq_bot.1 this)
  haveI : IsDiscreteValuationRing A :=
    ((IsDiscreteValuationRing.TFAE A hnf).out 0 4).2 (show (IsLocalRing.maximalIdeal A).IsPrincipal from ⟨_, hm⟩)
  haveI : IsFractionRing A K := Localization.subalgebra.isFractionRing_ofField K _ hp
  let V : ValuationSubring K :=
    { A.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, e⟩ | ⟨a, e⟩
        · exact Or.inl (e ▸ a.2)
        · exact Or.inr (e ▸ a.2) }
  have hc : ∀ a, c a ∈ V := fun a => A.algebraMap_mem (c0 a)
  let S : Place c := ⟨V, hc, ‹IsDiscreteValuationRing A›, by
    have e : c.codRestrict V hc = (algebraMap Q A).comp c0 := rfl
    rw [e]
    exact RingHom.EssFiniteType.comp hQ.essFiniteType
      ((RingHom.essFiniteType_algebraMap (R := Q) (S := A)).2
        (Algebra.EssFiniteType.of_isLocalization A p.primeCompl))⟩
  have hu : ∀ b : Q, b ∉ p → IsUnit (algebraMap Q A b) := fun b hb =>
    IsLocalization.map_units A (⟨b, hb⟩ : p.primeCompl)
  refine ⟨S, ⟨fun q hq => A.algebraMap_mem ⟨q, hq⟩, fun f hf => ?_⟩, ?_, fun P hP hne => ?_⟩
  · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj p.primeCompl (⟨f, hf⟩ : A)
    exact ⟨a, a.2, b.1, b.1.2, fun h => b.2 (by rw [show b.1 = 0 from Subtype.ext h]; exact p.zero_mem),
      S.ord_eq_zero (u := algebraMap Q A b.1) (hu _ b.2), congrArg Subtype.val e⟩
  · exact S.ord_irreducible (t := algebraMap Q A t)
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm)
  · by_contra h0
    have htK : (t : K) ≠ 0 := fun e => ht.ne_zero (Subtype.ext e)
    have h1 : 0 ≤ P.ord (t : K) := (P.ord_nonneg_iff htK).2 (hP.1 _ t.2)
    refine hne (ValuationSubring.eq_of_le_of_ne_top P.ring (fun f hf => ?_) S.ring_ne_top)
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 f hf
    have hbp : (⟨b, hb⟩ : Q) ∉ p := fun h => by
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 h
      have hd' : b = t * d := congrArg Subtype.val hd
      have hd0 : (d : K) ≠ 0 := fun h => hb0 (by rw [hd', h, mul_zero])
      have := (P.ord_nonneg_iff hd0).2 (hP.1 _ d.2)
      rw [hd', P.ord_mul htK hd0] at hbo
      omega
    obtain ⟨g, hg⟩ := (hu _ hbp).exists_right_inv
    have hg' : b * (g : K) = 1 := congrArg Subtype.val hg
    have : f = a * g := by rw [← e, mul_assoc, hg', mul_one]
    rw [this]
    exact A.mul_mem (A.algebraMap_mem ⟨a, ha⟩) g.2

end GlobalTheory.FieldPair.AdjModel
