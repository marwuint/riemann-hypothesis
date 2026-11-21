import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TheRec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

def IsTheRec (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h) : Prop :=
  IsRecLit h rc ∧ ∀ rc' : IrrGL (w.adicCompletion E) → WD h, IsRecLit h rc' → rc' = rc

def RecUnique : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc rc' : IrrGL (w.adicCompletion E) → WD h),
    IsRecLit h rc → IsRecLit h rc' → rc' = rc

end GlobalTheory.TheRec

end
