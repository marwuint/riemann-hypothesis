import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GLq

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT.Model

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

section Classes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem good_of_toral {x : IrrGL k} (hx : Toral x) : Good x := by
  obtain ⟨s, hs, hy⟩ := hx
  exact ⟨s, hs, fun y hys => Or.inl (hy y hys)⟩

end Classes

end GlobalTheory.RecT.Model

end
