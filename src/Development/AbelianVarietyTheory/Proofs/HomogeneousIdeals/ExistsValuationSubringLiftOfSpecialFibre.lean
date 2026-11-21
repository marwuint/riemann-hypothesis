import Mathlib

open IsLocalRing

namespace GlobalTheory

universe u

section Algebra

theorem height_le_one_of_forall_mem {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (m : Ideal B) [m.IsPrime] {f : B} (hf : f ≠ 0)
    (h : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → p ≤ m → f ∈ p) : m.height ≤ 1 := by
  by_cases hm : m = ⊥
  · subst hm
    simp
  have hfin := (Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hsub : (m : Set B) ⊆ ⋃ P ∈ (Ideal.span {f}).minimalPrimes, ((id P : Ideal B) : Set B) := by
    intro x hx
    simp only [Set.mem_iUnion, id, SetLike.mem_coe]
    by_cases hx0 : x = 0
    · obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr (h m inferInstance hm le_rfl))
      exact ⟨P, hP, hx0 ▸ P.zero_mem⟩
    obtain ⟨P, hP, hPm⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {x}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr hx)
    have hPp : P.IsPrime := hP.1.1
    have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hP.1.2
    have hP1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
    have hfP : f ∈ P := h P hPp (fun e => hx0 (by simpa [e] using hxP)) hPm
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := P)
        ((Ideal.span_singleton_le_iff_mem _).mpr hfP)
    have hQp : Q.IsPrime := hQ.1.1
    have hfQ : f ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.1.2
    have hQ0 : ⊥ < Q := bot_lt_iff_ne_bot.mpr fun e => hf (by simpa [e] using hfQ)
    refine ⟨Q, hQ, ?_⟩
    rcases hQP.eq_or_lt with e | hlt
    · exact e ▸ hxP
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hQ0
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h3 : (⊥ : Ideal B).height + 1 + 1 ≤ 1 := (add_le_add h1 le_rfl).trans (h2.trans hP1)
      simp at h3
      exact absurd h3 (by decide)
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime_finite hfin (f := id) ⊥ ⊥
    (fun i hi _ _ => hi.1.1)).mp hsub
  have hPp : P.IsPrime := hP.1.1
  exact (Ideal.height_mono hmP).trans
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)

theorem exists_notMem_forall_mem_minimalPrimes {B : Type*} [CommRing B] [IsNoetherianRing B]
    (I p : Ideal B) [p.IsPrime] (hp : ∀ P ∈ I.minimalPrimes, P ≤ p → P = p) :
    ∃ s ∉ p, ∀ P ∈ I.minimalPrimes, P ≠ p → s ∈ P := by
  classical
  have hfin : (I.minimalPrimes \ {p}).Finite :=
    I.finite_minimalPrimes_of_isNoetherianRing.subset Set.sdiff_subset
  have : ¬ hfin.toFinset.inf id ≤ p := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨P, hP, hle⟩
    rw [Set.Finite.mem_toFinset] at hP
    exact hP.2 (hp P hP.1 hle)
  obtain ⟨s, hs, hsp⟩ := SetLike.not_le_iff_exists.mp this
  refine ⟨s, hsp, fun P hP hne => ?_⟩
  exact (Finset.inf_le (f := id) (hfin.mem_toFinset.mpr ⟨hP, hne⟩) : _ ≤ P) hs

theorem quasiFiniteAt_of_height_le_one {O B : Type*} [CommRing O] [IsNoetherianRing O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    (m : Ideal B) [hm : m.IsMaximal] (h1 : m.height ≤ 1) (π : O) (hπ : algebraMap O B π ≠ 0)
    (hπm : algebraMap O B π ∈ m) : Algebra.QuasiFiniteAt O m := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  obtain ⟨s, hsm, hs⟩ := exists_notMem_forall_mem_minimalPrimes
    (Ideal.span {algebraMap O B π}) m (fun P hP hle => by
      have hPp : P.IsPrime := hP.1.1
      have hfP : algebraMap O B π ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hP.1.2
      have hP0 : ⊥ < P := bot_lt_iff_ne_bot.mpr fun e => hπ (by simpa [e] using hfP)
      by_contra hne
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP0
      have h3 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
      have h4 : (⊥ : Ideal B).height + 1 + 1 ≤ 1 := (add_le_add h2 le_rfl).trans (h3.trans h1)
      simp at h4
      exact absurd h4 (by decide))
  refine Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber (R := O) ⟨m, inferInstance⟩ ?_
  refine isOpen_induced_iff.mpr ⟨PrimeSpectrum.basicOpen s, (PrimeSpectrum.basicOpen s).isOpen, ?_⟩
  ext ⟨q, hq⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
    Set.mem_singleton_iff]
  constructor
  · intro hsq
    have hπq : algebraMap O B π ∈ q.asIdeal := by
      have : π ∈ (PrimeSpectrum.comap (algebraMap O B) q).asIdeal := by
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hq
        rw [hq]
        exact hπm
      exact this
    obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le (J := q.asIdeal)
      ((Ideal.span_singleton_le_iff_mem _).mpr hπq)
    have hPm : P = m := by
      by_contra hne
      exact hsq (hPq (hs P hP hne))
    subst hPm
    exact Subtype.ext <| PrimeSpectrum.ext (hm.eq_of_le q.isPrime.ne_top hPq).symm
  · intro e
    obtain rfl : q = ⟨m, inferInstance⟩ := congrArg Subtype.val e
    exact hsm

theorem exists_valuationSubring_of_height_le_one {O K : Type*} {B : Type u} [CommRing O]
    [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    (hinj : Function.Injective (algebraMap O B))
    (m : Ideal B) [hm : m.IsMaximal] (h1 : m.height ≤ 1) (π : O) (hπ : π ≠ 0)
    (hπm : algebraMap O B π ∈ m) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (φ : B →+* O'),
      (∀ a : O, (φ (algebraMap O B a) : K') = algebraMap K K' (algebraMap O K a)) ∧
      Function.Injective φ ∧ (maximalIdeal O').comap φ = m := by
  have hq : Algebra.QuasiFiniteAt O m := quasiFiniteAt_of_height_le_one m h1 π
    (fun e => hπ (hinj (by simpa using e))) hπm
  let K' := FractionRing B
  let L := Localization.AtPrime m
  let g : L →ₐ[B] K' := IsLocalization.liftAlgHom (M := m.primeCompl) (f := Algebra.ofId B K')
    (fun y => by
      have : (y : B) ≠ 0 := fun e => y.2 (e ▸ m.zero_mem)
      exact IsUnit.mk0 _ (by simpa [K'] using this))
  have hqK : Algebra.QuasiFinite O K' := by
    refine .of_forall_exists_mul_mem_range (g.restrictScalars O) fun x => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hb' : algebraMap B K' b ≠ 0 := by
      simpa [K'] using nonZeroDivisors.ne_zero hb
    refine ⟨algebraMap B L b, ?_, algebraMap B L a, ?_⟩
    · have : (g.restrictScalars O) (algebraMap B L b) = algebraMap B K' b := g.commutes b
      rw [this]
      exact IsUnit.mk0 _ hb'
    · simp [div_mul_cancel₀ _ hb']
  have hOK' : Function.Injective (algebraMap O K') := by
    rw [IsScalarTower.algebraMap_eq O B K']
    exact (IsFractionRing.injective B K').comp hinj
  let _ : Algebra K K' := (IsFractionRing.lift (K := K) hOK').toAlgebra
  have hst : IsScalarTower O K K' := .of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.QuasiFinite K K' := .of_restrictScalars O K K'
  obtain ⟨O', hO', hloc⟩ := IsLocalRing.exists_factor_valuationRing (g : L →+* K')
  let ψ : L →+* O' := (g : L →+* K').codRestrict O'.toSubring hO'
  have hψ : IsLocalHom ψ := hloc
  have hval : ∀ b : B, ((ψ.comp (algebraMap B L)) b : K') = algebraMap B K' b := fun b =>
    g.commutes b
  refine ⟨K', inferInstance, inferInstance, .of_quasiFinite, O', ψ.comp (algebraMap B L),
    fun a => ?_, fun a b hab => ?_, ?_⟩
  · rw [hval, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · apply IsFractionRing.injective B K'
    rw [← hval, ← hval, hab]
  · rw [← Ideal.comap_comap, maximalIdeal_comap ψ]
    exact IsLocalization.AtPrime.under_maximalIdeal L m

theorem exists_mem_height_map_le_one {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : Ideal A) [m.IsPrime] {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (h : ∃ p ∈ U, p.asIdeal ≤ m) :
    ∃ q ∈ U, q.asIdeal ≤ m ∧ (m.map (Ideal.Quotient.mk q.asIdeal)).height ≤ 1 := by
  obtain ⟨p₀, hp₀, hp₀m⟩ := h
  obtain ⟨I, ⟨q, ⟨hqU, hqm⟩, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian A A)
    (PrimeSpectrum.asIdeal '' {p | p ∈ U ∧ p.asIdeal ≤ m}) ⟨_, p₀, ⟨hp₀, hp₀m⟩, rfl⟩
  refine ⟨q, hqU, hqm, ?_⟩
  obtain ⟨_, ⟨f, rfl⟩, hfq, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqU hU
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by simpa using hqm)
  refine height_le_one_of_forall_mem _ (f := Ideal.Quotient.mk q.asIdeal f)
    (fun e => hfq (Ideal.Quotient.eq_zero_iff_mem.mp e)) fun p hp hp0 hpm => ?_
  by_contra hfp
  let p' : PrimeSpectrum A := ⟨p.comap (Ideal.Quotient.mk q.asIdeal), inferInstance⟩
  have hle : q.asIdeal ≤ p'.asIdeal := fun x hx => by
    change Ideal.Quotient.mk q.asIdeal x ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact p.zero_mem
  have hp'm : p'.asIdeal ≤ m := by
    refine (Ideal.comap_mono hpm).trans ?_
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_le le_rfl hqm
  refine hmax p'.asIdeal ⟨p', ⟨hfU hfp, hp'm⟩, rfl⟩ (lt_of_le_of_ne hle fun e => hp0 ?_)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := hsurj x
  have : x ∈ q.asIdeal := e ▸ hx
  simpa using Ideal.Quotient.eq_zero_iff_mem.mpr this

end Algebra

end GlobalTheory
