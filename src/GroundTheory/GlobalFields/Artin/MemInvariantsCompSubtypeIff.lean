import Mathlib
import GroundTheory.GlobalFields.Artin.LogCharpoly

noncomputable section

open IsDedekindDomain NumberField Polynomial

open scoped Pointwise

namespace GroundTheory.Global

section Inertia

variable {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S]

theorem mem_inertia_smul_iff (P : Ideal S) (h σ : G) :
    σ ∈ (h • P).inertia G ↔ h⁻¹ * σ * h ∈ P.inertia G := by
  constructor
  · intro hσ x
    have := hσ (h • x)
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem] at this
    simpa [mul_smul, smul_sub] using this
  · intro hσ x
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [mul_smul, smul_sub] using hσ (h⁻¹ • x)

theorem mul_mul_inv_mem_inertia {P : Ideal S} {s i : G} (hs : s ∈ MulAction.stabilizer G P)
    (hi : i ∈ P.inertia G) : s * i * s⁻¹ ∈ P.inertia G := by
  have hsP : s • P = P := hs
  rw [← hsP, mem_inertia_smul_iff, show s⁻¹ * (s * i * s⁻¹) * s = i by group]
  exact hi

end Inertia

section Place

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))

omit [NumberField L] [IsGalois K L] in
theorem exists_liesOver : ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal := by
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  refine ⟨⟨Q, hQmax.isPrime, fun h => v.ne_bot ?_⟩, hQ⟩
  rw [hQ.over, h]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

def placeAbove : HeightOneSpectrum (𝓞 L) :=
  (exists_liesOver (L := L) v).choose

instance liesOver_placeAbove : (placeAbove (L := L) v).asIdeal.LiesOver v.asIdeal :=
  (exists_liesOver (L := L) v).choose_spec

end Place

end GroundTheory.Global
