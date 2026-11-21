import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

theorem genericSpecMap_closedPoint (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] :
    _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L (IsLocalRing.closedPoint L) =
      genericPoint Z := by
  have h : (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)))
      (IsLocalRing.closedPoint (CommRingCat.of L)) = IsLocalRing.closedPoint Z.functionField :=
    Spec_closedPoint
  exact (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)))
    (Z.fromSpecStalk (genericPoint Z)) (IsLocalRing.closedPoint (CommRingCat.of L))).trans
    (h ▸ Scheme.fromSpecStalk_closedPoint)

theorem genericSpecMap_app_iso (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] (U : Z.Opens) (hη : genericPoint Z ∈ U)
    (hmem : _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L (IsLocalRing.closedPoint L) ∈ U) :
    (_root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L).app U ≫
      ((Spec (CommRingCat.of L)).presheaf.mapIso (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫
        Scheme.ΓSpecIso (CommRingCat.of L)).hom =
      Z.presheaf.germ U (genericPoint Z) hη ≫ CommRingCat.ofHom (algebraMap Z.functionField L) := by
  have h := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
    (CommRingCat.ofHom (algebraMap Z.functionField L)) U hmem
  exact (Scheme.germ_stalkClosedPointTo _ U hmem).symm.trans h

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
