import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.LocDefs
import Mathlib

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}

theorem WDN.charpoly (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (k : WDN ι r y) (g : ↥(Weil h)) :
    (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = y.charPol g := by
  obtain ⟨x, hx, k⟩ := k
  have e := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  rw [← hN.charPol_wdOf hl ht ι g, e, k.pol]

end UpperTheory.GalN.V
