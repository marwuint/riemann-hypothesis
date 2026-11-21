import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.EulerTw
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.GamInert

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

omit [IsCMField E] in
theorem pLoc_idem (T : Finset (Pl E)) (w : Pl E) : pLoc E w (idem E T) = if w ∈ T then 1 else 0 := rfl

end GlobalTheory.EulerTw.GamInert
