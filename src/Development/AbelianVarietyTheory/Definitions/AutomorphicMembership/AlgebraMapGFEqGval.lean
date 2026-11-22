import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntPair Formalism.BasicNotions
open Formalism.MainNotions.S (FlagG ZhatOM IsInCell ptMat)
open Formalism.MainNotions.S.Lat (LFlag hS Tu gS)

namespace GlobalTheory.IntTerm

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {A : Matrix (Fin S.rank) (Fin (r + 1)) E}

def colVec (S : HSpace E) {a : Type} (A : Matrix (Fin S.rank) a E) (b : a) : S.V :=
  S.frame.equivFun.symm fun i => A i b

end Space

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u u' : D.what₂.Word}

end Record

end GlobalTheory.IntTerm
