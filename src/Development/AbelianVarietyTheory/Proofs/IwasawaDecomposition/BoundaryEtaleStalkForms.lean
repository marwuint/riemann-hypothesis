import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameOfFreeSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataPsiValuationEqHalfForm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormBaseChangeDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralClosureFiniteLocalCompleteMixedChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocus

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.FarTrait

section Algebra
open Polynomial

theorem exists_coefficientField (S : Type) [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [CharZero (ResidueField S)] :
    ∃ Λ : Subring S, IsField Λ ∧ ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S := by
  let T : Set (Subring S) := {Λ | ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0}
  have hbot : (⊥ : Subring S) ∈ T := by
    intro x hx hm
    obtain ⟨n, rfl⟩ := Subring.mem_bot.1 hx
    rw [← residue_eq_zero_iff, map_intCast, Int.cast_eq_zero] at hm
    simp [hm]
  obtain ⟨Λ, -, hΛ⟩ := zorn_le_nonempty₀ T (fun c hc hch y hy => by
    refine ⟨sSup c, fun x hx => ?_, fun z hz => le_sSup hz⟩
    obtain ⟨K, hK, hxK⟩ := (Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hx
    exact hc hK x hxK) ⊥ hbot
  have hT : ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0 := hΛ.prop
  have hF : IsField Λ := by
    refine ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩
    have hu : IsUnit (x : S) := by
      by_contra h
      exact hx (Subtype.ext (hT _ x.2 h))
    let Λ' : Subring S :=
      { carrier := {s | ∃ n : ℕ, (x : S) ^ n * s ∈ Λ}
        one_mem' := ⟨0, by simp⟩
        zero_mem' := ⟨0, by simp⟩
        mul_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by convert Λ.mul_mem hn hm using 1; ring⟩
        add_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by
            convert Λ.add_mem (Λ.mul_mem (Λ.pow_mem x.2 m) hn) (Λ.mul_mem (Λ.pow_mem x.2 n) hm) using 1; ring⟩
        neg_mem' := by
          rintro a ⟨n, hn⟩
          exact ⟨n, by convert Λ.neg_mem hn using 1; ring⟩ }
    have h' : Λ' ∈ T := by
      rintro s ⟨n, hn⟩ hm
      exact (hu.pow n).mul_right_eq_zero.1 (hT _ hn (Ideal.mul_mem_left _ _ hm))
    have hle : Λ' ≤ Λ := hΛ.le_of_ge h' fun s hs => ⟨0, by simpa using hs⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    exact ⟨⟨y, hle ⟨1, by rw [pow_one, hy]; exact Λ.one_mem⟩⟩, Subtype.ext hy⟩
  refine ⟨Λ, hF, fun s => ?_⟩
  letI := hF.toField
  have key : ∀ a : S, (∀ f : Λ[X], aeval a f ∈ maximalIdeal S → aeval a f = 0) → a ∈ Λ := fun a ha => by
    have h' : (aeval (R := Λ) a).toRingHom.range ∈ T := by
      rintro _ ⟨f, rfl⟩ hm
      exact ha f hm
    exact hΛ.le_of_ge h' (fun y hy => ⟨C ⟨y, hy⟩, by simp; rfl⟩) ⟨X, by simp⟩
  have hres : ∀ (a : S) (f : Λ[X]), residue S (aeval a f) = aeval (residue S a) f := fun a f =>
    (aeval_algHom_apply (IsScalarTower.toAlgHom Λ S (ResidueField S)) a f).symm
  by_cases hs : IsAlgebraic Λ (residue S s)
  · have hi := hs.isIntegral
    haveI : CharZero Λ := RingHom.charZero (algebraMap Λ (ResidueField S))
    have hsep : (minpoly Λ (residue S s)).Separable := (minpoly.irreducible hi).separable
    obtain ⟨a, ha, has⟩ := HenselianRing.is_henselian (I := maximalIdeal S)
      ((minpoly Λ (residue S s)).map (algebraMap Λ S)) ((minpoly.monic hi).map _) s
      (by rw [eval_map_algebraMap, ← residue_eq_zero_iff, hres, minpoly.aeval])
      (by
        rw [derivative_map, eval_map_algebraMap]
        have := hsep.aeval_derivative_ne_zero (minpoly.aeval Λ (residue S s))
        rw [← hres] at this
        exact (isUnit_iff_ne_zero (G₀ := ResidueField S)).2 this)
    have e : residue S a = residue S s := by rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact has
    refine ⟨a, key a fun f hf => ?_, by rw [← neg_sub]; exact neg_mem has⟩
    rw [← residue_eq_zero_iff, hres, e] at hf
    obtain ⟨q, rfl⟩ := minpoly.dvd _ _ hf
    rw [IsRoot.def, eval_map_algebraMap] at ha
    rw [map_mul, ha, zero_mul]
  · refine ⟨s, key s fun f hf => ?_, by simp⟩
    rw [← residue_eq_zero_iff, hres] at hf
    by_contra h
    exact hs ⟨f, by rintro rfl; simp at h, hf⟩

end Algebra

open MvPowerSeries GlobalTheory.CohenStructure in

theorem exists_finite_over_normal (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S]
    [IsNoetherianRing S] [hc : IsAdicComplete (maximalIdeal S) S] :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (i : A →+* S),
      Function.Injective i ∧ i.Finite ∧ IsNoetherianRing A ∧ IsIntegrallyClosed A := by
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField S)
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with h | rfl
  · obtain ⟨A, _, _, _, i, h1, h2, h3, h4, -⟩ := exists_finite_injective_of_isAdicComplete S p h
      (by rw [← residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ p) inferInstance hc
    exact ⟨A, inferInstance, inferInstance, i, h1, h2, h3, h4⟩
  haveI := CharP.charP_to_charZero (ResidueField S)
  by_cases hm : maximalIdeal S = ⊥
  · letI := (isField_iff_maximalIdeal_eq.2 hm).toField
    exact ⟨S, inferInstance, inferInstance, RingHom.id S, Function.injective_id, RingHom.Finite.id S, inferInstance,
      inferInstance⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨Λ, hF, h1⟩ := exists_coefficientField S
  letI := hF.toField
  obtain ⟨n, x₀, hx₀, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S a ha0 ha
  let x : Fin (n + 1) → S := Fin.cons a x₀
  have hx : ∀ i, x i ∈ maximalIdeal S := fun i => Fin.cases ha hx₀ i
  let A := MvPowerSeries (Fin (n + 1)) Λ
  let φ : A →ₐ[Λ] S := mvEvalAdic Λ (maximalIdeal S) x hx
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := isDomain_mvPowerSeries Λ (n + 1)
  have hb : maximalIdeal Λ = ⊥ := isField_iff_maximalIdeal_eq.1 hF
  have : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance
  have hA := isAdicComplete_mvPowerSeries Λ (n + 1)
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => by simpa [φ] using hx j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hb, Ideal.mem_bot] at h5
    rwa [h5, map_zero, sub_zero] at h4
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rw [← Fin.range_cons]
    rintro _ ⟨i, rfl⟩
    show x i ∈ _
    rw [← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]
    exact Ideal.mem_map_of_mem (algebraMap A S)
      (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, ha, h⟩ := h1 s
    refine ⟨C ⟨a, ha⟩, ?_⟩
    rwa [show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  refine ⟨A, inferInstance, inferInstance, algebraMap A S,
    injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin, inferInstance,
    isIntegrallyClosed_mvPowerSeries Λ (n + 1)⟩
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]

theorem exists_factor {R W : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CharZero W] (g : R →+* W) :
    ∃ (N : Type) (_ : CommRing N) (_ : IsDomain N) (_ : IsLocalRing N) (φ : R →+* N) (g' : N →+* W),
      IsCN N ∧ IsLocalHom φ ∧ Function.Injective g' ∧ ∀ r, g' (φ r) = g r := by
  haveI := RingHom.ker_isPrime g
  let S := R ⧸ RingHom.ker g
  let k : S →+* W := RingHom.kerLift g
  have hk : Function.Injective k := RingHom.kerLift_injective g
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  haveI : IsAdicComplete (maximalIdeal S) S := CompleteFiniteExtension.isAdicComplete_of_finite_local R S
  haveI : CharZero S := RingHom.charZero k
  obtain ⟨A, _, _, i, hi, hfin, _, _⟩ := exists_finite_over_normal S
  letI : Algebra A S := i.toAlgebra
  have : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hi
  have : Module.Finite A S := hfin
  let N := integralClosure S (FractionRing S)
  have hf : Module.Finite S N := finite_normalisation_of_finite_over_normal A S
  haveI : IsLocalRing N := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := S) _
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp k) := (IsFractionRing.injective W _).comp hk
  let K : FractionRing S →+* FractionRing W := IsFractionRing.lift j
  have hK : ∀ s, K (algebraMap S _ s) = algebraMap W _ (k s) := IsFractionRing.lift_algebraMap j
  have hint : ∀ x : N, K x ∈ (algebraMap W (FractionRing W)).range := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.map_of_comp_eq k K (RingHom.ext fun s => (hK s).symm) x.2)
  let eW : W ≃+* (algebraMap W (FractionRing W)).range :=
    RingEquiv.ofBijective (algebraMap W (FractionRing W)).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective W (FractionRing W) (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩
  let g' : N →+* W := eW.symm.toRingHom.comp ((K.comp N.val.toRingHom).codRestrict _ hint)
  have hg' : ∀ x : N, algebraMap W (FractionRing W) (g' x) = K x := fun x =>
    congrArg Subtype.val (eW.apply_symm_apply ⟨K x, hint x⟩)
  have hinj : Function.Injective g' := fun a b h =>
    Subtype.ext (K.injective ((hg' a).symm.trans ((congrArg _ h).trans (hg' b))))
  haveI : FaithfulSMul S N := (faithfulSMul_iff_algebraMap_injective S N).2 fun a b h =>
    IsFractionRing.injective S (FractionRing S) (congrArg Subtype.val h)
  haveI : IsLocalHom (Ideal.Quotient.mk (RingHom.ker g)) := IsLocalHom.of_surjective (S := S) _ Ideal.Quotient.mk_surjective
  refine ⟨N, inferInstance, inferInstance, inferInstance, (algebraMap S N).comp (Ideal.Quotient.mk _), g',
    ⟨IsNoetherianRing.of_finite S _, integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing S),
      CompleteFiniteExtension.isAdicComplete_of_finite_local S _, RingHom.charZero g'⟩, inferInstance, hinj, fun r => ?_⟩
  exact IsFractionRing.injective W (FractionRing W) ((hg' _).trans (hK _))

end GlobalTheory.FarTrait
