import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AlgebraicPointIntegral
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedModPow

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

section SlopeTestRemainingChoices

open Polynomial

private theorem algpt_int {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {R : Type} [CommRing R] [Algebra O R] [IsLocalRing R]
    {K : Type} [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K)
    (a : R) (ha : a ∈ maximalIdeal R) : IsIntegral O (f a) :=
  _root_.UpperTheory.Reformulated.B.AlgebraicPointIntegral.algpt_int f a ha

private theorem algpt_pow {O S : Type} [CommRing O] [CommRing S] [Algebra O S] [IsNoetherianRing S] (m : Ideal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ m) (n : ℕ) :
    ∃ N : Submodule O S, N.FG ∧ ∀ x : S, ∃ y ∈ N, x - y ∈ m ^ n :=
  _root_.UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow m hres n

private theorem algpt_finite {O S : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing S] [Algebra O S] [IsLocalRing S] [IsNoetherianRing S] [Algebra.IsIntegral O S]
    (hloc : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ maximalIdeal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ maximalIdeal S) : Module.Finite O S := by
  set J : Ideal S := (maximalIdeal O).map (algebraMap O S) with hJ
  have hJle : J ≤ maximalIdeal S := Ideal.map_le_iff_le_comap.2 hloc
  have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hJle))
  haveI : IsHausdorff (maximalIdeal O) S :=
    IsHausdorff.map_algebraMap_iff.1 (IsHausdorff.of_isLocalRing J S hJne)
  have hrad : maximalIdeal S ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hJP, hP⟩
    have h1 : maximalIdeal O ≤ P.comap (algebraMap O S) := Ideal.map_le_iff_le_comap.1 hJP
    have h2 : P.comap (algebraMap O S) = maximalIdeal O :=
      ((maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) h1).symm
    have h3 : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) P
      (h2 ▸ maximalIdeal.isMaximal O)
    exact (eq_maximalIdeal h3).ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨N, hN, h⟩ := algpt_pow (maximalIdeal S) hres n
  refine (UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) S).2 ⟨?_⟩
  have : (⊤ : Submodule O (S ⧸ (maximalIdeal O) • (⊤ : Submodule O S))) = N.map (Submodule.mkQ _) := by
    symm
    rw [Submodule.map_mkQ_eq_top, eq_top_iff]
    intro x _
    obtain ⟨y, hy, h1⟩ := h x
    have h2 : x - y ∈ (maximalIdeal O) • (⊤ : Submodule O S) := by
      rw [Ideal.smul_top_eq_map]
      exact hn h1
    simpa using Submodule.add_mem_sup h2 hy
  rw [this]
  exact hN.map _

end SlopeTestRemainingChoices

theorem UpperTheory.V.W.exists_algebraicPoint_of_groupDeterminant :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (K : Type) [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K), Module.Finite O f.range := by
  intro O _ _ _ _ R _ _ _ K _ _ _ _ f
  have hint : ∀ a : R, IsIntegral O (f a) := by
    intro a
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    have h1 : IsIntegral O (f (a - algebraMap O R c)) := algpt_int f _ hc
    have h2 : f a = f (a - algebraMap O R c) + algebraMap O _ c := by simp
    rw [h2]
    exact h1.add isIntegral_algebraMap
  let g : R →ₐ[O] f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' (g : R →+* f.range) hg
  haveI : IsNoetherianRing f.range := isNoetherianRing_of_surjective R _ (g : R →+* f.range) hg
  haveI : IsLocalHom (g : R →+* f.range) := IsLocalHom.of_surjective _ hg
  have hm : ∀ a ∈ maximalIdeal R, g a ∈ maximalIdeal f.range := fun a ha =>
    map_nonunit (g : R →+* f.range) a ha
  haveI : Algebra.IsIntegral O f.range := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hg x
    exact (isIntegral_algHom_iff f.range.val Subtype.val_injective).1 (hint a)⟩
  exact algpt_finite
    (fun a ha => by
      rw [← g.commutes]
      exact hm _ (map_nonunit (algebraMap O R) a ha))
    (fun x => by
      obtain ⟨a, rfl⟩ := hg x
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
      exact ⟨c, by simpa using hm _ hc⟩)
