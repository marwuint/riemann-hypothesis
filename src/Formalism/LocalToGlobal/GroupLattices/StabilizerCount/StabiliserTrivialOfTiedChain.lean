import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite
import Formalism.LocalToGlobal.HermitianColumns.TiedQC

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.G.StabilizerCardinality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Stab0Used (D : D7) : Prop :=
  (∀ u c, Nat.card ((D.mem u).C.stab 0 c) = 1) ∧
    ∀ u μ, DV.Used D μ → ∀ c, Nat.card ((D.chTw u μ).stab 0 c) = 1

theorem card_stab0_mem (D : D7) (lev : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    Nat.card ((D.mem u).C.stab 0 c) = 1 := by
  have := Formalism.L2.G.Triv.stabZero_rec D lev u c
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩

theorem stab0Used_iff (D : D7) : Stab0Used D ↔ Formalism.MainNotions.OrbitPlaces.Stab0 D := Iff.rfl

end Formalism.L2.G.StabilizerCardinality

end
