import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

noncomputable section

namespace GlobalTheory.NT

open Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField IsDedekindDomain

def mult {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

section Hecke

variable {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def IsFrob (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) : Prop :=
  ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver 𝔭.asIdeal ∧ ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P

def InInertia (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) : Prop :=
  ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver 𝔭.asIdeal ∧ ∀ x : 𝓞 L, σ • x - x ∈ P

def UnramIn (𝔭 : HeightOneSpectrum (𝓞 K)) : Prop := ∀ σ : L ≃ₐ[K] L, InInertia L 𝔭 σ → σ = 1

open Classical in

def heckeVal (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if h : (∀ σ, InInertia L 𝔭 σ → χ σ = 1) ∧ ∃ σ, IsFrob L 𝔭 σ then ((χ h.2.choose : ℂˣ) : ℂ) else 0

open Classical in

def heckeIdeal (χ : (L ≃ₐ[K] L) →* ℂˣ) (I : Ideal (𝓞 K)) : ℂ :=
  ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 K), heckeVal L χ 𝔭 ^ (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors

def RayPair (𝔪 : Ideal (𝓞 K)) (α β : 𝓞 K) : Prop :=
  α ≠ 0 ∧ β ≠ 0 ∧ IsCoprime (Ideal.span {α}) 𝔪 ∧ IsCoprime (Ideal.span {β}) 𝔪 ∧ α - β ∈ 𝔪 ∧
    ∀ φ : K →+* ℝ, 0 < φ (α : K) * φ (β : K)

def IsModulus (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔪 : Ideal (𝓞 K)) : Prop :=
  𝔪 ≠ ⊥ ∧ (∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 → heckeVal L χ 𝔭 ≠ 0) ∧
    ∀ α β : 𝓞 K, RayPair 𝔪 α β → heckeIdeal L χ (Ideal.span {α}) = heckeIdeal L χ (Ideal.span {β})

omit [NumberField K] [NumberField L] in

instance smulCommClass_gal_integers : SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm s a x := by
    apply RingOfIntegers.ext
    rw [Algebra.smul_def, Algebra.smul_def]
    change s (algebraMap K L a * x) = algebraMap K L a * s x
    rw [map_mul, AlgEquiv.commutes]

theorem isFrob_iff (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) :
    IsFrob L 𝔭 σ ↔ ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver 𝔭.asIdeal ∧ IsArithFrobAt (𝓞 K) σ P := by
  refine exists_congr fun P => and_congr_right fun _ => and_congr_right fun hP => ?_
  have h : P.under (𝓞 K) = 𝔭.asIdeal := hP.over.symm
  unfold IsArithFrobAt AlgHom.IsArithFrobAt
  rw [h, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem inInertia_iff (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) :
    InInertia L 𝔭 σ ↔ ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver 𝔭.asIdeal ∧ σ ∈ P.inertia (L ≃ₐ[K] L) :=
  Iff.rfl

theorem exists_isFrob [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) : ∃ σ : L ≃ₐ[K] L, IsFrob L 𝔭 σ := by
  have := 𝔭.isPrime
  obtain ⟨P, hP, hP'⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 L)))
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P
  exact ⟨σ, (isFrob_iff L 𝔭 σ).2 ⟨P, hP, hP', hσ⟩⟩

theorem heckeVal_eq [IsGalois K L] (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 K))
    (hχ : ∀ τ, InInertia L 𝔭 τ → χ τ = 1) {σ : L ≃ₐ[K] L} (hσ : IsFrob L 𝔭 σ) :
    heckeVal L χ 𝔭 = (χ σ : ℂˣ) := by
  have h : (∀ σ, InInertia L 𝔭 σ → χ σ = 1) ∧ ∃ σ, IsFrob L 𝔭 σ := ⟨hχ, σ, hσ⟩
  unfold heckeVal
  rw [dif_pos h]
  obtain ⟨P, hP, hPo, h1⟩ := (isFrob_iff L 𝔭 _).1 h.2.choose_spec
  obtain ⟨P', hP', hPo', h2⟩ := (isFrob_iff L 𝔭 _).1 hσ
  have := 𝔭.isPrime
  obtain ⟨τ, hτ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) P' P
    (hPo'.over.symm.trans hPo.over)
  have h3 := h2.conj τ
  rw [← hτ] at h3
  have h4 := hχ _ ((inInertia_iff L 𝔭 _).2 ⟨P, hP, hPo, h1.mul_inv_mem_inertia h3⟩)
  simp only [map_mul, map_inv, mul_inv_eq_one] at h4
  rw [h4, mul_inv_cancel_comm]

theorem heckeVal_eq_zero (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 K))
    (hχ : ¬ ∀ τ, InInertia L 𝔭 τ → χ τ = 1) : heckeVal L χ 𝔭 = 0 := by
  unfold heckeVal
  rw [dif_neg fun h => hχ h.1]

theorem heckeVal_of_unramIn [IsGalois K L] (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hu : UnramIn L 𝔭) {σ : L ≃ₐ[K] L} (hσ : IsFrob L 𝔭 σ) : heckeVal L χ 𝔭 = (χ σ : ℂˣ) :=
  heckeVal_eq L χ 𝔭 (fun τ hτ => by rw [hu τ hτ, map_one]) hσ

end Hecke

end GlobalTheory.NT

end
