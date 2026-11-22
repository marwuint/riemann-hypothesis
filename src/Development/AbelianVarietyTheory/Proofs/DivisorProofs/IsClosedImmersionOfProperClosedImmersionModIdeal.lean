import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedEmptyOfUniversallyClosedOfLeJacobson
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericallyFiniteFiniteNearCodimOnePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSubsingletonOfClosedImmersionModIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSurjModIdealExistsCongrOneMulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestri
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSectionsModBaseIdealOfClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSubOneMemBaseIdealSheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionMorphismRestrictBasicOpenOfMulM

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
namespace GlobalTheory.ClosedLev

theorem exists_nhd (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z)
    (p : Z ⟶ Spec (CommRingCat.of R)) (hφ : IsProper φ)
    (hc : IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ)) (z : Z)
    (hz : I ≤ (p z).asIdeal) : ∃ U : Z.Opens, z ∈ U ∧ IsClosedImmersion (φ ∣_ U) := by
  have hfin : (⇑φ ⁻¹' {z}).Finite := (_root_.GlobalTheory.FormalAlg.fibre_subsingleton_of_isClosedImmersion_restrict R I X Z φ p hc z hz).finite
  obtain ⟨V₀, hzV₀, hV₀⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton φ z hfin
  obtain ⟨V, hV, hzV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens hzV₀
  have hVf : IsFinite (φ ∣_ V) := GlobalTheory.PushFinite.isFinite_restrict_of_le φ hle
  obtain ⟨haff, hfr⟩ := _root_.GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict X Z φ V hV hVf
  obtain ⟨r, hr1, hr⟩ := _root_.GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range _ _ (φ.app V).hom hfr _ (_root_.GlobalTheory.FormalAlg.surj_mod_baseIdeal_of_isClosedImmersion R I X Z φ p hc V hV haff)
  exact ⟨Z.basicOpen r, GlobalTheory.T.mem_basicOpen_of_sub_one_mem_baseIdealSheaf R I Z p V hV r z hzV hz hr1, _root_.GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range X Z φ V hV haff r hr⟩

theorem isClosedImmersion_of_mod : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsProper φ → UniversallyClosed p → IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → IsClosedImmersion φ := by
  intro R _ I hI X Z φ p hφ hp hc
  let O : Z.Opens := ⨆ U : {U : Z.Opens // IsClosedImmersion (φ ∣_ U)}, U.1
  have hO : O = ⊤ := by
    have h0 := _root_.GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson R I hI Z p hp ((O : Set Z)ᶜ) O.isOpen.isClosed_compl fun z hz hIz => by
      obtain ⟨U, hzU, hU⟩ := exists_nhd R I X Z φ p hφ hc z hIz
      exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hzU⟩)
    exact TopologicalSpace.Opens.ext (by simpa [Set.compl_empty_iff] using h0)
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun U : {U : Z.Opens // IsClosedImmersion (φ ∣_ U)} => U.1) hO fun U => U.2

end GlobalTheory.ClosedLev
