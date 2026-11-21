import Formalism.SubspaceCounting.StatementB

noncomputable section
open scoped BigOperators

namespace Formalism.G0.TopsWeightFunctionBounds

inductive St where
  | bad
  | good
  | run (K j d : ℕ) (al ev : Bool)
  deriving DecidableEq

def okG (L₂ j d : ℕ) (ev : Bool) : Bool :=
  if j = 0 then !ev else (decide ((d + 1) % 2 = 0) && decide (L₂ < 2 * (d + 1)))

def step (R L₂ : ℕ) : St → Bool → St
  | .bad, _ => .bad
  | .good, _ => .good
  | .run K j d al ev, false => .run K j (d + 1) al (!ev)
  | .run K j d al ev, true =>
      if j + 1 = R then
        (if (al && okG L₂ j d ev) = true then .good
         else if K ≤ 1 then .bad else .run (K - 1) 0 0 true (!ev))
      else .run K (j + 1) 0 (al && okG L₂ j d ev) (!ev)

def runS (R L₂ : ℕ) (s : St) (bs : List Bool) : St := bs.foldl (step R L₂) s

end Formalism.G0.TopsWeightFunctionBounds

noncomputable section
open scoped BigOperators

namespace Formalism.G0.TopsWeightFunctionBounds

end Formalism.G0.TopsWeightFunctionBounds

noncomputable section
open scoped BigOperators

namespace Formalism.G0.TopsWeightFunctionBounds

section sums
variable {R L₂ : ℕ} {δ : ℝ}

lemma runS_cons (s : St) (b : Bool) (bs : List Bool) :
    runS R L₂ s (b :: bs) = runS R L₂ (step R L₂ s b) bs := rfl

end sums

end Formalism.G0.TopsWeightFunctionBounds

noncomputable section
open scoped BigOperators

namespace Formalism.G0.TopsWeightFunctionBounds

end Formalism.G0.TopsWeightFunctionBounds

noncomputable section
open scoped BigOperators

namespace Formalism.G0.TopsWeightFunctionBounds

end Formalism.G0.TopsWeightFunctionBounds

namespace Formalism.G0

end Formalism.G0
