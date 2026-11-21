import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairLift
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems Formalism.L2.G.Model

theorem letterWt_anti (m d : ℕ) (vec : Bool) : Antitone (letterWt m d vec) := by
  intro i j hij
  have hl : i = Fin.last m → j = Fin.last m := fun hi => le_antisymm (Fin.le_last j) (hi ▸ hij)
  have h0 : j = 0 → i = 0 := fun hj => le_antisymm (hj ▸ hij) (Fin.zero_le i)
  unfold letterWt
  cases vec
  · simp only [Bool.false_eq_true, if_false]
    by_cases hj : j = Fin.last m
    · by_cases hi : i = Fin.last m
      · simp [hi, hj]
      · simp [hi, hj]
    · have hi : i ≠ Fin.last m := fun hi => hj (hl hi)
      simp [hi, hj]
  · simp only [if_true]
    by_cases hj : j = 0
    · simp [hj, h0 hj]
    · by_cases hi : i = 0
      · simp [hi, hj]
      · simp [hi, hj]

end Formalism.MainNotions.ColumnSystems.Pf
