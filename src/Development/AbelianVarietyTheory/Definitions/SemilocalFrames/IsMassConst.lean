import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

noncomputable section
open ValuativeRel IsDedekindDomain NumberField ComplexConjugate Formalism.MainNotions.S.Loc Matrix MeasureTheory
open scoped Classical

namespace GlobalTheory.SgGlob

section Rat
variable {E : Type} [Field E] [NumberField E]

def eps (K : Type) [CommRing K] (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal fun b => (-1) ^ (r - (b : ℕ))

end Rat

namespace ModFam
end ModFam

end GlobalTheory.SgGlob
