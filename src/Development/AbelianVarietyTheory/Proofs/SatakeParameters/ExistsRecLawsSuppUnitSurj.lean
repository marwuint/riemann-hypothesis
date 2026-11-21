import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.SplitRead

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem eig_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ) (σ : Weil h) :
    (WD.lpOfChar h ξ hξ).eig σ = {(ξ σ : ℂ)} := by
  rw [WD.lpOfChar, WD.eig_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

theorem cls_eq_ofChar (χ : (w.adicCompletion E)ˣ →* ℂˣ) (c : Irr (w.adicCompletion E) 1)
    (hc : Nonempty (c.π.Equiv (detRep (Fin 1) χ))) :
    ∃ hχ : IsSmoothChar χ, cls (toIrrRep c) = .ofChar χ hχ := by
  obtain ⟨φ⟩ := hc
  have h1 : IsSmoothChar (detChar (Fin 1) χ) := (isSmooth_ofChar_iff _).1
    ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)
  have h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
    Units.continuous_map (continuous_matrix fun i j => by
      rw [Subsingleton.elim i j]; simpa using continuous_id')
  have h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ := by
    refine MonoidHom.ext fun z => congrArg χ ?_
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  exact ⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩

end GlobalTheory.LocLanglands
