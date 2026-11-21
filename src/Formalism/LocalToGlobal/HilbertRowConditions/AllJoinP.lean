import Formalism.LocalToGlobal.HilbertRowConditions.AllJoin
import Formalism.LocalToGlobal.GlobalTheory.ConcNWeight
import Formalism.LocalToGlobal.GlobalTheory.ConcNP
import Formalism.LocalToGlobal.ClassRec

noncomputable section

set_option linter.dupNamespace false

namespace Formalism.L2.GlobalTheoryTheory.AllJoin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.ConcNWeight

section One

variable {D : D7}

theorem tieVecW_of_join {A : AllRows D} (hJ : AllJoinA A) : TieVecW A := by
  obtain ⟨ψ₀, hψ, h⟩ := hJ.level
  exact ⟨ψ₀, hψ, fun k v => Or.inr (h k v)⟩

theorem weight_of_join {A : AllRows D} (hL : admLq D) (hA : TieAdmG D) (hR : RangeW D) (hJ : AllJoinA A) :
    WeightAllRows A :=
  weightAllRows_of A hL hA hR (tieVecW_of_join hJ)

end One

end Formalism.L2.GlobalTheoryTheory.AllJoin

end
