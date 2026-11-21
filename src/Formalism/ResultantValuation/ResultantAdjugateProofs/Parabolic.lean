import Mathlib

noncomputable section

namespace Formalism.ResultantValuation

open Module

namespace ParabolicCounting

variable (F : Type) [Field F] (r t : ℕ)

@[instance_reducible] def act : MulAction (GL (Fin (r + t)) F) (Submodule F (Fin (r + t) → F)) where
  smul g W := W.map (Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F))
  one_smul W := by
    show W.map _ = W
    rw [Units.val_one, Matrix.mulVecLin_one, Submodule.map_id]
  mul_smul g h W := by
    show W.map _ = (W.map _).map _
    rw [Units.val_mul, Matrix.mulVecLin_mul, Submodule.map_comp]

attribute [local instance] act

theorem smul_def (g : GL (Fin (r + t)) F) (W : Submodule F (Fin (r + t) → F)) :
    g • W = W.map (Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F)) := rfl

end ParabolicCounting

end Formalism.ResultantValuation
