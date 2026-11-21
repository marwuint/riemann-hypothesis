import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.SecPowLoc

theorem fnOf_map {X : Scheme.{0}} [IsIntegral X] {U V : X.Opens} (i : V ⟶ U)
    (h : genericPoint X ∈ V) (a : Γ(X, U)) :
    fnOf V h (X.presheaf.map i.op a) = fnOf U (i.le h) a :=
  X.presheaf.germ_res_apply i _ h a

end GlobalTheory.Cartier.SecPowLoc

namespace GlobalTheory.Cartier

end GlobalTheory.Cartier
