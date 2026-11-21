import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsApplyEqZeroAndEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasAlgebraicChartsOfIsStandardSmooth
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero

namespace GlobalTheory.AffinePoints

open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff

section Null

theorem addHaar_image_eq_zero_of_finrank_lt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (h : finrank ℝ E < finrank ℝ F) {s : Set E} {f : E → F} (hf : DifferentiableOn ℝ f s) :
    μ (f '' s) = 0 := by
  obtain ⟨i, hi⟩ := finrank_le_iff_exists_linearMap.1 h.le
  obtain ⟨L, hL⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hsurj : Function.Surjective L := fun x => ⟨i x, DFunLike.congr_fun hL x⟩
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt h
  let L' : F →L[ℝ] E := LinearMap.toContinuousLinearMap L
  have him : f '' s = (f ∘ L') '' (L' ⁻¹' s) := by
    rw [image_comp, image_preimage_eq s (f := L') hsurj]
  rw [him]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (f' := fun x => (fderivWithin ℝ f s (L' x)).comp L') (fun x hx => ?_) (fun x _ => ?_)
  · exact (hf _ hx).hasFDerivWithinAt.comp x L'.hasFDerivWithinAt (mapsTo_preimage _ _)
  · refine LinearMap.det_eq_zero_iff_ker_ne_bot.2 fun h0 => hker (le_bot_iff.1 ?_)
    rw [← h0]
    intro v hv
    have : L' v = 0 := hv
    simp [this]

variable {d : ℕ}

theorem volume_image_eq_zero_of_finrank_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (h : finrank ℂ E < d) {s : Set E} {f : E → Fin d → ℂ}
    (hf : DifferentiableOn ℂ f s) : volume (f '' s) = 0 := by
  refine addHaar_image_eq_zero_of_finrank_lt volume ?_ (hf.restrictScalars ℝ)
  rw [finrank_real_of_complex, finrank_real_of_complex]
  simpa using h

end Null

section Algebra

universe u

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] {d : ℕ}

theorem faithfulSMul_and_isAlgebraic_of_etale (R S : Type*) [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [Algebra R S] [Algebra.Etale R S] :
    FaithfulSMul R S ∧ Algebra.IsAlgebraic R S := by
  haveI : FaithfulSMul R S := inferInstance
  exact ⟨this, isAlgebraic_of_quasiFiniteAt R S ⊥⟩

theorem trdeg_eq_of_etale [IsDomain A] (g : MvPolynomial (Fin d) K →ₐ[K] A) (hg : g.Etale) :
    Algebra.trdeg K A = d := by
  letI : Algebra (MvPolynomial (Fin d) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) A := hg
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  obtain ⟨_, _⟩ := faithfulSMul_and_isAlgebraic_of_etale (MvPolynomial (Fin d) K) A
  rw [trdeg_eq_of_isAlgebraic_top K (MvPolynomial (Fin d) K) A, MvPolynomial.trdeg_of_isDomain]
  simp

theorem ringKrullDim_eq_of_isStandardSmooth [IsDomain A]
    [Algebra.IsStandardSmoothOfRelativeDimension d K A] : ringKrullDim A = d := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d K A
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := K) (S := A) d
  exact ringKrullDim_eq_of_trdeg_eq K A (trdeg_eq_of_etale g hg)

theorem exists_notMem_isStandardSmoothOfRelativeDimension [IsDomain A] [Algebra.FiniteType K A]
    (hd : ringKrullDim A = d) (P : Ideal A) [P.IsPrime] [Algebra.IsSmoothAt K P] :
    ∃ s ∉ P, Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away s) := by
  haveI : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  obtain ⟨s, hs, ι, σ, _, _, ⟨Q⟩⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K P
  refine ⟨s, hs, ?_⟩
  have hs0 : Submonoid.powers s ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors fun h => hs (h ▸ P.zero_mem)
  haveI : IsDomain (Localization.Away s) := IsLocalization.isDomain_localization hs0
  haveI H : Algebra.IsStandardSmoothOfRelativeDimension Q.dimension K (Localization.Away s) :=
    Q.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    Q.dimension K (Localization.Away s)
  have h1 := trdeg_eq_of_etale g hg
  haveI : FaithfulSMul A (Localization.Away s) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hs0)
  haveI : Algebra.IsAlgebraic A (Localization.Away s) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers s)
  rw [trdeg_eq_of_isAlgebraic_top K A (Localization.Away s)] at h1
  have h2 := ringKrullDim_eq_of_trdeg_eq K A h1
  rw [hd] at h2
  obtain rfl : d = Q.dimension := by exact_mod_cast h2
  exact H

theorem exists_ne_zero_isStandardSmoothOfRelativeDimension [PerfectField K] [IsDomain A]
    [Algebra.FiniteType K A] (hd : ringKrullDim A = d) :
    ∃ s : A, s ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away s) := by
  haveI : Algebra.IsSmoothAt K (⊥ : Ideal A) := by
    haveI : IsLocalization (⊥ : Ideal A).primeCompl (FractionRing A) := by
      rw [Ideal.primeCompl_bot]; infer_instance
    let e := (IsLocalization.algEquiv (⊥ : Ideal A).primeCompl (FractionRing A)
      (Localization.AtPrime (⊥ : Ideal A))).restrictScalars K
    haveI : Algebra.EssFiniteType K (FractionRing A) := .comp K A _
    haveI : Algebra.FormallySmooth K (FractionRing A) := Algebra.FormallySmooth.of_perfectField
    exact Algebra.FormallySmooth.of_equiv e
  simpa using exists_notMem_isStandardSmoothOfRelativeDimension (K := K) hd ⊥

end Algebra

variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}

theorem volume_coords_image_zeroSet [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A)
    (hg : @Algebra.IsAlgebraic _ A _ _ g.toRingHom.toAlgebra) {f : A} (hf : f ≠ 0) :
    volume (coords g '' {p : A →ₐ[ℂ] ℂ | p f = 0}) = 0 := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := g.toRingHom.toAlgebra
  obtain ⟨r, hr, c, hc⟩ := (hg.isAlgebraic f).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hf)
  refine measure_mono_null ?_ (ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_of_ne_zero_fin d r hr)
  rintro _ ⟨p, hp, rfl⟩
  have h1 : eval (coords g p) r = p (g r) := aeval_coords g p r
  have h2 : g r = f * c := hc
  simp only [mem_compl_iff, mem_setOf_eq, not_not]
  rw [h1, h2, map_mul, hp, zero_mul]

theorem isOpenMap_coords [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (hg : g.Finite)
    (hinj : Function.Injective g) : IsOpenMap (coords g : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) :=
  (mvPolynomialHomeomorph ℂ ℂ (Fin d)).isOpenMap.comp (isOpenMap_comap g hg hinj)

theorem dense_compl_of_volume_coords_image [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A)
    (hg : g.Finite) (hinj : Function.Injective g) {S : Set (A →ₐ[ℂ] ℂ)}
    (hS : volume (coords g '' S) = 0) : Dense Sᶜ := by
  have h1 : Dense (coords g '' S)ᶜ :=
    Measure.dense_of_ae (μ := volume) (measure_eq_zero_iff_ae_notMem.1 hS)
  refine (h1.preimage (isOpenMap_coords g hg hinj)).mono ?_
  intro p hp hpS
  exact hp ⟨p, hpS, rfl⟩

theorem dense_nonvanishing [IsDomain A] [Algebra.FiniteType ℂ A] {f : A} (hf : f ≠ 0) :
    Dense {p : A →ₐ[ℂ] ℂ | p f ≠ 0} := by
  obtain ⟨s, g, hinj, hg⟩ := exists_finite_inj_algHom_of_fg ℂ A
  refine dense_compl_of_volume_coords_image g hg hinj (volume_coords_image_zeroSet g ?_ hf)
  letI := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) ℂ) A := hg
  infer_instance

end GlobalTheory.AffinePoints
