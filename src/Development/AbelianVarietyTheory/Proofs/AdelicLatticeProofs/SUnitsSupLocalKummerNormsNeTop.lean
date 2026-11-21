import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnitsPrimeDegree
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNorms
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCountPlacesNotLocalPowerLeIndex
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem sUnits_sup_finNorm_ne_top : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → sUnits F S ⊔ finNorm p F δ S ≠ ⊤ := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hr htop
  obtain ⟨h0, h1⟩ := _root_.GlobalTheory.CNorm.first_inequality_sUnits_prime p F ζ δ S hp hζ hS hδ hr
  obtain ⟨-, h2⟩ := _root_.GlobalTheory.CNorm.pow_tNon_le_index_finNorm p F ζ δ S hp hζ
  have hle : kNorm p (RingHom.id F) (δ : F) ≤ finNorm p F δ S :=
    le_iInf₂ fun _ _ => (_root_.GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map p hp.pos).2 F _ _ _
  have h3 : (finNorm p F δ S).index = (finNorm p F δ S).relIndex (sUnits F S) := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
  have h4 := Subgroup.relIndex_le_of_le_left hle h0
  have h5 := Nat.mul_le_mul_right ((kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S)) hp.two_le
  omega

end GlobalTheory.CNorm
