import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotIsobaricRigid
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualFiniteIdelicIffLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualInfinityInfinitesimalIffFieStatement

noncomputable section

namespace GlobalTheory.HeightCounting.TrueSide

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Family

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7}
  (T : GlobalTheory.RowTie.WDTie D.nd D.naut)

def ofU {R : Ranks} {H : Formalism.BasicNotions.Host R} (χ : HChar H.E) (h : χ.IsUnitary) : HostCGu H 1 :=
  haveI := host_isCMField H; ⟨CG.ofChar χ, CG.isUnitary_ofChar h⟩

theorem eq_ofU {R : Ranks} {H : Formalism.BasicNotions.Host R} (σ : HostCGu H 1) :
    haveI := host_isCMField H; σ = ofU (CGu.equivChar H.E σ).1 (CGu.equivChar H.E σ).2 :=
  haveI := host_isCMField H; Subtype.ext (CGu.ofChar_equivChar σ).symm

theorem unr_symm (w) (x) : D.naut.unr ((T.e w).symm x) ↔ x.unr := by rw [T.unr, Equiv.apply_symm_apply]

theorem frob_symm (w) (x) (h : x.unr) : D.naut.frobEig ((T.e w).symm x) = x.frobEig := by
  rw [T.frobEig _ _ ((unr_symm T w x).2 h), Equiv.apply_symm_apply]

end Family

section Side

theorem csdFin {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) : haveI := host_isCMField H;
    (∀ u : (Af H.E)ˣ, χ.1 (finId H.E (Units.map (conjFin (IsCMField.complexConj H.E).toRingEquiv).toMonoidHom u)⁻¹) =
      χ.1 (finId H.E u)) ↔
    ∀ w w', IsConjPl H w w' → ∀ k : H.Eˣ,
      χ.locK w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.locK w k)⁻¹ := GlobalTheory.T.heckeChar_conjSelfDual_finite_idelic_iff_local H χ

theorem csdInf {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) : haveI := host_isCMField H;
    (∀ z, dchi χ (-star z) = dchi χ z) ↔
    ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹ := GlobalTheory.T.heckeChar_conjSelfDual_infinity_infinitesimal_iff_field H χ

theorem isCsd_ofChar_iff {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) :
    haveI := host_isCMField H; (CG.ofChar χ).IsCsd ↔ IsCSD H χ := by
  haveI := host_isCMField H
  rw [CG.isCsd_ofChar, CG.thetaInv_one_iff, csdFin H χ, csdInf H χ]
  rfl

theorem infChar_ofChar_of_hasInfQ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) (a : R.Psi → ℚ)
    (h : χ.HasInfQ (embPsi H) a) (g : R.Psi) : haveI := host_isCMField H;
    (CG.ofChar χ).infChar (embPsi H g) = {(a g : ℂ)} ∧
      (CG.ofChar χ).infChar ((starRingEnd ℂ).comp (embPsi H g)) = {-(a g : ℂ)} := by
  haveI := host_isCMField H
  obtain ⟨n, hn, hi⟩ := h
  have hI : Function.Injective fun i => InfinitePlace.mk (embPsi H i) := fun i j e => by
    rcases InfinitePlace.mk_eq_iff.1 e with e | e
    · exact GlobalTheory.HalfIntChars.embPsi_inj H e
    · exact (GlobalTheory.HalfIntChars.embPsi_ne_conj H j i (e.symm.trans (RingHom.ext fun x => rfl))).elim
  have h3 := (InfType.expo_of_infType _ χ).2.2 _ _ _ hI hi g
  have ha : ((n g : ℂ) / 2) = (a g : ℂ) := by
    have := hn g
    have e : (a g : ℂ) = ((a g : ℚ) : ℂ) := rfl
    rw [e, show (a g : ℚ) = (n g : ℚ) / 2 by rw [this]; ring]
    push_cast; ring
  refine ⟨by rw [CG.infChar_ofChar, h3.1, ha], ?_⟩
  rw [show (starRingEnd ℂ).comp (embPsi H g) = ComplexEmbedding.conjugate (embPsi H g) from RingHom.ext fun x => rfl,
    CG.infChar_ofChar, h3.2, neg_div, ha]

end Side

section Main

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7}
  (T : GlobalTheory.RowTie.WDTie D.nd D.naut)

theorem equivChar_ofU {R : Ranks} {H : Formalism.BasicNotions.Host R} (χ : HChar H.E) (h : χ.IsUnitary) :
    haveI := host_isCMField H; (CGu.equivChar H.E (ofU χ h)).1 = χ :=
  haveI := host_isCMField H; CG.toChar_ofChar χ

theorem exists_ofU {R : Ranks} {H : Formalism.BasicNotions.Host R} (σ : HostCGu H 1) : ∃ χ h, σ = ofU χ h :=
  ⟨_, _, eq_ofU σ⟩

end Main

end GlobalTheory.HeightCounting.TrueSide

namespace GlobalTheory.HeightCounting

end GlobalTheory.HeightCounting

end
