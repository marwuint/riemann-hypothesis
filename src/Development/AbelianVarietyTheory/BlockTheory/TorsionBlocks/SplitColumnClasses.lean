import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG

def SplitsCompletely (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  p.Prime ∧ (Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E

theorem splitsCompletely_g (D : D7) (i : Fin 2) : SplitsCompletely D.host.E (D.host.g i) :=
  ⟨D.host.g_prime i, D.nd.g_split i⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

end
