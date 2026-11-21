import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.IrrCharIff

noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT

namespace PI.SerBridgeGLW

section
variable {G : Type} [Group G] [Fintype G]

theorem isChar_of_fdrep (V : FDRep ℂ G) : IsChar V.character := by
  classical
  let b := Module.finBasis ℂ V
  refine ⟨Module.finrank ℂ V,
    MonoidHom.toHomUnits ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp V.ρ), fun x => ?_⟩
  simp [FDRep.character, LinearMap.trace_eq_matrix_trace ℂ b]
  rfl

theorem ipG_eq (hC : ConjChar) (V : FDRep ℂ G) :
    ipG V.character V.character = ∑ x, V.character x * V.character x⁻¹ := by
  unfold ipG
  exact Finset.sum_congr rfl fun x _ => by rw [hC G V x]

theorem isIrrChar_of_simple (hC : ConjChar) (V : FDRep ℂ G) [Simple V] : IsIrrChar V.character := by
  refine ⟨isChar_of_fdrep V, ?_⟩
  rw [ipG_eq hC, (FDRep.simple_iff_char_is_norm_one V).mp inferInstance, Nat.card_eq_fintype_card]

def repOfGL {n : ℕ} (ρ : G →* GL (Fin n) ℂ) : FDRep ℂ G :=
  FDRep.of (((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin n → ℂ)).toRingEquiv.toMonoidHom).comp
    ((Units.coeHom _).comp ρ))

theorem repOfGL_character {n : ℕ} (ρ : G →* GL (Fin n) ℂ) (x : G) :
    (repOfGL ρ).character x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ) := by
  change LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLinAlgEquiv' (ρ x : Matrix (Fin n) (Fin n) ℂ)) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
  congr 1
  exact LinearMap.toMatrix'_toLin' _

theorem irrCharIff_of (hC : ConjChar) : IrrCharIff := by
  intro G _ _ χ
  constructor
  · rintro ⟨⟨n, ρ, hρ⟩, hip⟩
    have hχ : χ = (repOfGL ρ).character := funext fun x => by rw [hρ, repOfGL_character]
    subst hχ
    refine ⟨repOfGL ρ, ?_, rfl⟩
    rw [FDRep.simple_iff_char_is_norm_one, ← ipG_eq hC, hip, Nat.card_eq_fintype_card]
  · rintro ⟨V, hV, rfl⟩
    exact isIrrChar_of_simple hC V

end

end PI.SerBridgeGLW
