import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace PositivityTheory.Rg.BcB.FC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

abbrev Fam (E : Type) [Field E] [NumberField E] (a b : ℕ) : Type := ∀ w : Pl E, GLw a w × GLw b w → ℂ

end PositivityTheory.Rg.BcB.FC

end
