import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.Curves

open Matrix
open scoped ContDiff

noncomputable section

namespace CCRuleCW

open Formalism.FourierDecayAlt

section sup

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def apO (ops : List (Bool × B.Mat k r)) (f : B.Mat k r → E) : B.Mat k r → E :=
  ops.foldl (fun f o => act o f) f

@[simp] theorem apO_nil (f : B.Mat k r → E) : apO [] f = f := rfl

@[simp] theorem apO_cons (o : Bool × B.Mat k r) (os : List (Bool × B.Mat k r)) (f : B.Mat k r → E) :
    apO (o :: os) f = apO os (act o f) := rfl

end sup

end CCRuleCW
