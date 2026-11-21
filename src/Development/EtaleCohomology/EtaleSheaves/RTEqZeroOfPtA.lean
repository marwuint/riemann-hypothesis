import Development.EtaleCohomology.EtaleSheaves.LeafDegCut
import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKill1V2Cut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem goal_of' (hN : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd) (hW : LateralTheory.E.SecondDegreeKilling.LeafPtW)
    (hV : LateralTheory.E.SecondDegreeKilling.LeafPtV) : LateralTheory.E.LeafDegCut.LeafKill1 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV' p g1 g2 hp hp1 hp2 hSHV U y
  refine LateralTheory.E.SecondDegreeKilling.Nbhd.killPt_of hN hH q k hq i s ι (g2 ≫ g1 ≫ p) hp2 U 1 (gY q i (g1 ≫ p) g2 ι U 1 y) ?_
  intro A _ t hA
  by_cases h : Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B)
  · exact hV hH q k hq i s ι V hV' (g1 ≫ p) g2 hp1 hp2 U A t hA h 1 (hSHV A (t ≫ U.hom) hA h).2.2.1 y
  · have := hW hH q k hq i s ι V hV' (g2 ≫ g1 ≫ p) hp2 A (t ≫ U.hom) hA h 1
    exact Subsingleton.elim _ _

end LateralTheory.E.LeafKill1V2Cut
