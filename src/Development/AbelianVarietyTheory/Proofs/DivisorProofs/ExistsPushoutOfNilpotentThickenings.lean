import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackAppOfIsBasisOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutThickeningsOfIsPullbackSections
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem exists_pushout_of_nilpotent_thickenings : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ → (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₁.app U).hom)) → (∀ U : Y₂.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₂.app U).hom)) → ∃ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsPushout i₁ i₂ j₁ j₂ ∧ IsClosedImmersion j₁ ∧ IsClosedImmersion j₂ ∧ ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  intro Y₀ Y₁ Y₂ i₁ i₂ h1 h2 s1 s2 n1 n2
  obtain ⟨Y, j₁, j₂, hw, c1, c2, t1, t2, 𝒱, hb, hp⟩ := _root_.GlobalTheory.FerrandPush.exists_pushout_data Y₀ Y₁ Y₂ i₁ i₂ h1 h2 s1 s2 n1 n2
  have hall := _root_.GlobalTheory.PinchBasis.isPullback_app_of_isBasis Y₀ Y₁ Y₂ Y i₁ i₂ j₁ j₂ hw 𝒱 hb hp
  exact ⟨Y, j₁, j₂, hw, _root_.GlobalTheory.ThickPush.isPushout_of_isPullback_sections Y₀ Y₁ Y₂ i₁ i₂ h1 h2 s1 s2 Y j₁ j₂ hw c1 c2 t1 t2 hall,
    c1, c2, hall⟩

end GlobalTheory
