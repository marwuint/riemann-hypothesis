import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open scoped Pointwise

private theorem move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F))) :
    ∃ (B : ValuationSubring Ω) (g : G F Ω), IsPlaceOver B w ∧ (∀ x, x ∈ B ↔ g x ∈ A) ∧
      (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  obtain ⟨B, hB⟩ := (exists_isPlaceOver Ω w : ∃ B : ValuationSubring Ω, IsPlaceOver B w)
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hm : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hv : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hm, ← hm, map_eq_zero_iff _ g.injective]
  have hD : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  refine ⟨B, g, hB, hm, hD, fun s hs => ⟨hD s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hv]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hm y).2 (((g • B).valuation_le_one_iff _).1 hx)))

private theorem nat_mem_under {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (χ : Γ →* C) (g s : Γ) : χ (g * s * g⁻¹) = χ s := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

private theorem rep_conj {Γ C : Type} [Group Γ] [Group C] (r : Γ →* C) (P : C) (g s : Γ) :
    P * r g * r s * (P * r g)⁻¹ = P * r (g * s * g⁻¹) * P⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group

