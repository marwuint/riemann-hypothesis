import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.Comp

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

variable {hc : CMData F E} {S : HSpace E} {N : ℕ}

def Coord.Q (K : Coord hc S n) (co : S.V ≃ₗ[E] (Fin N → E)) : Matrix (Fin N) n E :=
  LinearMap.toMatrix' ((K.κ.symm.trans co : (n → E) ≃ₗ[E] (Fin N → E)) : (n → E) →ₗ[E] (Fin N → E))

end Formalism.L2.GlobalTheoryTheory.Comp

end
