import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeckeIdealEqOfRay

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.FieldsEx

variable {E : Type} [Field E] [NumberField E] {h : ℕ}

theorem one_mem_pow : (1 : E) ∈ powIdealElts E h :=
  ⟨one_ne_zero, 1, by rw [one_pow, FractionalIdeal.spanSingleton_one]⟩

theorem mul_mem_pow {x y : E} (hx : x ∈ powIdealElts E h) (hy : y ∈ powIdealElts E h) :
    x * y ∈ powIdealElts E h := by
  obtain ⟨hx0, a, ha⟩ := hx
  obtain ⟨hy0, b, hb⟩ := hy
  exact ⟨mul_ne_zero hx0 hy0, a * b, by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ha, hb, mul_pow]⟩

theorem inv_mem_pow {x : E} (hx : x ∈ powIdealElts E h) : x⁻¹ ∈ powIdealElts E h := by
  obtain ⟨hx0, a, ha⟩ := hx
  exact ⟨inv_ne_zero hx0, a⁻¹, by rw [← FractionalIdeal.spanSingleton_inv, ha, inv_pow]⟩

theorem npow_mem_pow {x : E} (hx : x ∈ powIdealElts E h) (n : ℕ) : x ^ n ∈ powIdealElts E h := by
  induction n with
  | zero => rw [pow_zero]; exact one_mem_pow
  | succ n ih => rw [pow_succ]; exact mul_mem_pow ih hx

theorem zpow_mem_pow {x : E} (hx : x ∈ powIdealElts E h) (n : ℤ) : x ^ n ∈ powIdealElts E h := by
  cases n with
  | ofNat n => simpa using npow_mem_pow hx n
  | negSucc n => rw [zpow_negSucc]; exact inv_mem_pow (npow_mem_pow hx _)

theorem prod_mem_pow {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, f i ∈ powIdealElts E h) :
    ∏ i ∈ s, f i ∈ powIdealElts E h :=
  Finset.prod_induction f (· ∈ powIdealElts E h) (fun _ _ => mul_mem_pow) one_mem_pow hf

theorem map_mem_pow {E' : Type} [Field E'] [NumberField E'] (σ : E →+* E') {x : E} (hx : x ∈ powIdealElts E h) :
    σ x ∈ powIdealElts E' h := by
  obtain ⟨hx0, a, ha⟩ := hx
  have hle : (𝓞 E)⁰ ≤ Submonoid.comap (RingOfIntegers.mapRingHom σ) (𝓞 E')⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ fun a b hab =>
      RingOfIntegers.ext (σ.injective (congrArg (fun y : 𝓞 E' => (y : E')) hab))
  have hm : IsLocalization.map E' (RingOfIntegers.mapRingHom σ) hle = σ :=
    IsLocalization.ringHom_ext (𝓞 E)⁰ (by rw [IsLocalization.map_comp]; rfl)
  refine ⟨(map_ne_zero σ).2 hx0, FractionalIdeal.extendedHom' E' hle a, ?_⟩
  rw [← map_pow, ← ha]
  change _ = FractionalIdeal.extended E' _ _
  rw [FractionalIdeal.extended_spanSingleton, hm]

theorem exists_aut [IsGalois ℚ E] (φ τ : E →+* ℂ) : ∃ σ : E ≃ₐ[ℚ] E, ∀ x, τ x = φ (σ x) := by
  letI := φ.toAlgebra
  let t : E →ₐ[ℚ] ℂ := τ.toRatAlgHom
  exact ⟨t.restrictNormal' E, fun x => (t.restrictNormal_commutes E x).symm⟩

theorem exists_gen (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ γ : 𝓞 E, γ ≠ 0 ∧ 𝔞 ^ classNumber E = Ideal.span {γ} := by
  let 𝔠 : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
  have h1 : ClassGroup.mk0 (𝔠 ^ classNumber E) = 1 := by
    rw [map_pow, classNumber, pow_card_eq_one]
  obtain ⟨γ, hγ⟩ := (ClassGroup.mk0_eq_one_iff (𝔠 ^ classNumber E).2).1 h1
  have hγ' : 𝔞 ^ classNumber E = Ideal.span {γ} := hγ
  refine ⟨γ, ?_, hγ'⟩
  rintro rfl
  rw [Ideal.span_singleton_zero] at hγ'
  exact pow_ne_zero _ h𝔞 hγ'

theorem span_eq_extend (K : IntermediateField ℚ ℂ) [NumberField K] (τ : E →+* ℂ) (hK : ∀ x, τ x ∈ K)
    (𝔞 : Ideal (𝓞 E)) : Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} =
      extendIdealHom (τ.codRestrict K hK) 𝔞 := by
  refine Eq.trans ?_ (span_image_eq_coeSubmodule_map (τ.codRestrict K hK) 𝔞)
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
  rfl

end GlobalTheory.Mem.FieldsEx

end
