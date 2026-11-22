import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.FamilyPartFiveOfExplicitConstants

noncomputable section

namespace GlobalTheory.DataRowsCounterexample

open Formalism.BasicNotions Formalism.MainNotions

theorem places_nonempty (D : D7) : Nonempty D.what₂.Tau ∧ Nonempty D.what₂.Word :=
  ⟨⟨D.eTau.symm 1⟩, ⟨D.u₀⟩⟩

end GlobalTheory.DataRowsCounterexample
