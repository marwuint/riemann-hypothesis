import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitZetaAct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffConjOfQExpansionConj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexRingEquivExtendingSubfieldAut
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelNFunctionGaloisConjQExpansion
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_conj_of_inR : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω) (f : ℍ → ℂ), InR ε.range f → ∃ f' : ℍ → ℂ, InR ε.range f' ∧ ∀ h h' : HahnSeries ℚ Ω, IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s f hf
  obtain ⟨N, w, hN, hLv⟩ := hf
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.FN.exists_ringEquiv_extend_of_embedding Ω ε s
  have hgE : ∀ x ∈ ε.range, g x ∈ ε.range := by
    rintro x ⟨y, rfl⟩
    exact ⟨s y, (hg y).symm⟩
  obtain ⟨d, hd⟩ := GlobalTheory.WpFam.exists_unit_zetaAct N g
  obtain ⟨f', hLv', hconj⟩ := _root_.GlobalTheory.FN.lv_galois_conj g ε.range N d w f hgE hd hLv
  refine ⟨f', ⟨N, w, hN, hLv'⟩, ?_⟩
  intro h h' hh hh' r
  have h1 : dg d * redGL N 1 = redGL N 1 * dg d := by
    rw [GlobalTheory.WpFam.Act.redGL_one]; simp
  have hc := hconj 1 1 h1
  simp only [one_smul] at hc
  have hq := hLv.2 1
  simp only [one_smul] at hq
  exact _root_.GlobalTheory.FN.exp_conj Ω ε s.toRingHom g N w f f' h h' hg hN hq hc hh hh' r

end GlobalTheory.FN
