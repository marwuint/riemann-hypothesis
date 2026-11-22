import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ArcIntegral

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := (Spec.map_comp _ _).symm

theorem ev_factor {Z : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z₁ : Sp A ⟶ Z) (z₂ : Sp B ⟶ Z)
    (e : z₂ = spMap φ ≫ z₁) (W : Z.Opens) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ W) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ W) (f : Γ(Z, W)) :
    ev z₂ W h₂ f = φ (ev z₁ W h₁ f) := by
  subst e
  rw [GlobalTheory.FlagMod.ev_spMap φ z₁ W h₁]
  rfl

theorem point_cases (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : Sp R) :
    (∃ p : Sp K, spMap (algebraMap R K) p = x) ∨ x = IsLocalRing.closedPoint R := by
  by_cases h : x.asIdeal = ⊥
  · refine Or.inl ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [h]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  · refine Or.inr (PrimeSpectrum.ext ?_)
    exact IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal h)

theorem spMap_closedPoint {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (f : A →+* B)
    [IsLocalHom f] : spMap f (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A :=
  IsLocalRing.comap_closedPoint f

theorem spMap_closedPoint_of_surjective {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    spMap f (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A :=
  haveI : (IsLocalRing.closedPoint B).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal B
  PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f hf))

theorem mk_le_continuum_of_finite {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (hg : g.Finite)
    (hA : Cardinal.mk A ≤ Cardinal.continuum) : Cardinal.mk B ≤ Cardinal.continuum := by
  letI := g.toAlgebra
  haveI : Module.Finite A B := hg
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A B
  refine (Cardinal.mk_le_of_surjective hf).trans ?_
  rw [show Cardinal.mk (Fin n → A) = Cardinal.mk A ^ n by simp]
  exact (pow_le_pow_left' hA n).trans (Cardinal.power_nat_le Cardinal.aleph0_le_continuum)

theorem mem_range_of_map {R K A B : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] [IsDomain A] [Field B] [Algebra A B] [IsFractionRing A B] (e : R →+* A)
    [IsLocalHom e] (la : K →+* B) (hla : ∀ r, la (algebraMap R K r) = algebraMap A B (e r)) (x : K)
    (hx : la x ∈ (algebraMap A B).range) : x ∈ (algebraMap R K).range := by
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r, hr⟩
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨t, ht⟩ := hx
  have h1 : algebraMap A B (e r * t) = 1 := by
    rw [map_mul, ht, ← hla, show algebraMap R K r = x⁻¹ from hr, ← map_mul, inv_mul_cancel₀ h0, map_one]
  have h2 : e r * t = 1 := IsFractionRing.injective A B (h1.trans (map_one _).symm)
  have hu : IsUnit r := isUnit_of_map_unit e r (IsUnit.of_mul_eq_one _ h2)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨(u⁻¹ : Rˣ), ?_⟩
  have h3 : algebraMap R K ((u⁻¹ : Rˣ) : R) * x⁻¹ = 1 := by
    rw [← show algebraMap R K u = x⁻¹ from hr, ← map_mul, Units.inv_mul, map_one]
  exact (mul_inv_eq_one₀ (inv_ne_zero h0 |> fun h => by simpa using h)).1 h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem range_j_subset {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨x, rfl⟩
  have h : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨x, rfl⟩
  rw [Model.j, Scheme.Hom.comp_apply]
  exact h

theorem exists_frac_lift {A K L : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
    (f : A →+* L) (hf : Function.Injective f) : ∃ fK : K →+* L, fK.comp (algebraMap A K) = f :=
  ⟨IsFractionRing.lift hf, RingHom.ext fun x => by rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap hf x]⟩

theorem exists_away_lift {A S L : Type} [CommRing A] [CommRing S] [Algebra A S] (x : A) [IsLocalization.Away x S]
    [CommRing L] (f : A →+* L) (hf : IsUnit (f x)) : ∃ F : S →+* L, ∀ a, F (algebraMap A S a) = f a :=
  ⟨IsLocalization.Away.lift x hf, IsLocalization.Away.lift_eq x hf⟩

theorem isUnit_map_X {A : Type} [CommRing A] (κ : A →+* ℂ) :
    IsUnit ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ) PowerSeries.X) := by
  rw [RingHom.comp_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  exact isUnit_iff_ne_zero.2 (HahnSeries.single_ne_zero one_ne_zero)

end GlobalTheory.ArcIntegral
