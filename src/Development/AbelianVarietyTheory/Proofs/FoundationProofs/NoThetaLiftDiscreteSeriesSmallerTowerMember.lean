import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaTensorIntertwinerLowerTowerMembers

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.TowerDrop

theorem archimedeanRallisFourth_of_discreteSeriesBlattner : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFourth X := by
  intro X _ _ hD h5
  refine ⟨fun t al be ga de hd i hi hr hs MM f hf => ?_,
    fun t al be ga de hd i hi hr hs MM f hf => ?_⟩
  · exact ((GlobalTheory.LowerTower.no_map_lower X hD h5 t al be ga de hd.1 i hi).1 hr hs) MM f hf
  · have hA := hd.1
    have ht : 1 ≤ t := hA.1
    have hn : 1 ≤ al.length + be.length + ga.length + de.length := hA.2.1
    have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
    obtain ⟨-, hpar, -⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t al be ga de hA
    obtain ⟨-, -, hsign, -⟩ := _root_.GlobalTheory.TypesMirror.types_mirror t al be ga de hA
    have hno := (_root_.GlobalTheory.LowestTypeDrop.lowestType_not_jointShape t al be ga de hA i hi).2.1 hr hs
    refine GlobalTheory.LowerTower.tensNo_first X hD h5 (by omega) _ hpar 0 ?_ hno MM f hf
    rw [GlobalTheory.SmallerSource.cPair_sub hr hs]
    refine fun a => ⟨(hsign a).1, fun h => (hsign a).2 (lt_of_le_of_ne h fun h0 => ?_)⟩
    have := hA.2.2.2.2.2.2.2.2.2.2 _ (GlobalTheory.LowerTower.lamA_mem al be ga de a)
    rw [h0, abs_zero] at this
    linarith

end GlobalTheory.TowerDrop
