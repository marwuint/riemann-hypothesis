import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistenceOfComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniformisedChartAfterValuationRingExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtension

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.DetHT

theorem exists_lift_int {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
    (Y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {K : Type} [Field K] (z : Sp K ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = z := by
  obtain ⟨g, hg⟩ : ∃ g : 𝓞 c.F →+* K, z ≫ Y.s = spMap g := ⟨(Spec.preimage (z ≫ Y.s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨x, hx⟩ := h ⟨(default : PrimeSpectrum K), rfl⟩
  have e : Y.j ≫ Y.s = (Y.jQ ≫ pullback.snd _ _) ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨q, e1⟩ : ∃ q : PrimeSpectrum c.F,
      PrimeSpectrum.comap g default = PrimeSpectrum.comap (algebraMap (𝓞 c.F) c.F) q := by
    have e2 : (z ≫ Y.s) (default : PrimeSpectrum K) = (Y.j ≫ Y.s) x := congrArg Y.s hx.symm
    rw [hg, e] at e2
    exact ⟨_, e2⟩
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun v hv => ?_
    have h1 : v ∈ (PrimeSpectrum.comap g default).asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hv]; exact zero_mem _
    rw [e1, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
    rw [Ideal.eq_bot_of_prime q.asIdeal] at h1
    exact IsFractionRing.injective (𝓞 c.F) c.F (h1.trans (map_zero _).symm)
  let g' : c.F →+* K := IsFractionRing.lift hinj
  have hg' : spMap g' ≫ spMap (algebraMap (𝓞 c.F) c.F) = spMap g := by
    rw [← Spec.map_comp]
    congr 1
    ext v
    exact IsFractionRing.lift_algebraMap hinj v
  let z' : Sp K ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift z (spMap g') (hg.trans hg'.symm)
  have hz' : z' ≫ pullback.fst _ _ = z := pullback.lift_fst _ _ _
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have := Y.jQ_open
  have hr : Set.range z' ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    refine ⟨x, (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective ?_⟩
    have e3 : (z' ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) (default : PrimeSpectrum K) =
        z (default : PrimeSpectrum K) := by
      rw [hz']
    exact hx.trans e3.symm
  refine ⟨IsOpenImmersion.lift Y.jQ z' hr, ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz']

end GlobalTheory.DetHT

end
