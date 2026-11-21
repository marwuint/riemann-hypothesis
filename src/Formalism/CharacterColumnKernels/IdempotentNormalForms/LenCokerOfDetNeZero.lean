import Formalism.CharacterColumnKernels.StatementX
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SingleEqSmul
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero

open Finset Module IsDiscreteValuationRing Matrix

noncomputable section

namespace Formalism.NG

section KerHomAux

variable {R : Type*} [Ring R] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {g d : Type} [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
  (ρ : R →+* Matrix d d O)

def uncurryEquiv : (g → LatQ O d ρ) ≃ₗ[O] (g × d → KO O) where
  toFun v p := v p.1 p.2
  invFun w j b := w (j, b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable [SMulCommClass R O (LatQ O d ρ)]

end KerHomAux

end Formalism.NG
