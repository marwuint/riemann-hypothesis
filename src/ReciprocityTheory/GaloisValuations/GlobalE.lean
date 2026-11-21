import ReciprocityTheory.GaloisValuations.GlobalEA

noncomputable section

open NumberField IsDedekindDomain Pointwise Polynomial

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp

section split

variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {A : ValuationSubring Ω}

private theorem mem_decompositionSubgroup_iff_galois_valuations {K : Type*} [Field K] [Algebra K Ω] {B : ValuationSubring Ω}
    {σ : Ω ≃ₐ[K] Ω} : σ ∈ B.decompositionSubgroup K ↔ ∀ x, σ x ∈ B ↔ x ∈ B := by
  constructor
  · intro h x
    have h' : σ • B = B := h
    have e := ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := B) (x := x)
    rw [h'] at e
    exact e
  · intro h
    show σ • B = B
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h (σ⁻¹ • x), AlgEquiv.smul_def]
    rw [show σ (σ⁻¹ x) = x from AlgEquiv.apply_symm_apply σ x]

theorem resGal_mem_Dec_iff {σ : G L Ω} :
    resGal F L Ω σ ∈ Dec (F := F) A ↔ σ ∈ Dec (F := L) A := by
  show resGal F L Ω σ ∈ A.decompositionSubgroup F ↔ σ ∈ A.decompositionSubgroup L
  rw [mem_decompositionSubgroup_iff_galois_valuations, mem_decompositionSubgroup_iff_galois_valuations]
  simp only [resGal_apply]

variable (F L) in

def decRes (A : ValuationSubring Ω) : Dec (F := L) A →* Dec (F := F) A :=
  ((resGal F L Ω).comp (Dec (F := L) A).subtype).codRestrict (Dec (F := F) A)
    (fun σ => resGal_mem_Dec_iff.mpr σ.2)

theorem decRes_apply (σ : Dec (F := L) A) : (decRes F L A σ : G F Ω) = resGal F L Ω σ := rfl

theorem one_lt_normV (v : HeightOneSpectrum (𝓞 F)) : 1 < normV v := by
  have e : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [e]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

end split

end ReciprocityTheory.Gal
