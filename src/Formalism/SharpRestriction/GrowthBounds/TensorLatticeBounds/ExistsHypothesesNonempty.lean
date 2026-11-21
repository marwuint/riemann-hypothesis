import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.LocalRingCardinality.SpanPowerMembership.GatSetting
import Formalism.SharpRestriction.GrowthBounds.DefsInst
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.FrobeniusOrbits

def GatHasPlaces (D : D7) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), 0 < (D.gat u w hg).P.nV

theorem gatHasPlaces_of_ties {D : D7} (hT : GatTies D) : GatHasPlaces D := by
  intro u w hg
  obtain ⟨v, _⟩ := (hT.gat_pos u w hg).symm (D.eTau.symm 1)
  exact lt_of_le_of_lt (Nat.zero_le _) v.isLt

end Formalism.MainNotions.G.Inhab

end
