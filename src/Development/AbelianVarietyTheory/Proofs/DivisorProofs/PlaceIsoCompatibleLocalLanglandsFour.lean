import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL GlobalTheory.TheRecTransport

namespace GlobalTheory.LawsTTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem eig_of_wdRel {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (H : WDRel φ y y') {σ : Weil h} {σ' : Weil h'}
    (hσ : WeilRel φ σ σ') : y.eig σ = y'.eig σ' := by
  obtain ⟨n, b, b', e1, e2, -, hb⟩ := H
  rw [← e1, ← e2, WD.eig, WD.eig, WD.charPol_mk, WD.charPol_mk, hb σ _ hσ]

end GlobalTheory.LawsTTransport

