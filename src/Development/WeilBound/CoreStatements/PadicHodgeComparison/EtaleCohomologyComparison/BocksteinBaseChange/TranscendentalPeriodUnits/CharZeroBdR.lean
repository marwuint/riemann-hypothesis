import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.CrystallineSemistableComparison
import GroundTheory.PAdicHodge.WAFracMain

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

instance charZero_bdR : CharZero (BdR l) := ⟨fun a b h => by
  have : qQ l (a : ℚ_[l]) = qQ l (b : ℚ_[l]) := by rw [map_natCast, map_natCast]; exact h
  exact Nat.cast_injective ((qQ l).injective this)⟩

variable (l) in

abbrev Fr : Subfield (BdR l) :=
  ACris.fracBCris (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one

end CrystallineSemistableComparison
