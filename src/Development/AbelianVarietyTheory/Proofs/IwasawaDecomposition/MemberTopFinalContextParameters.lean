import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesEqMassesOfUnfold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LayeredAutomorphicDataExistsOfTwoPasses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayeredDataOfGoodScaleContexts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem memberTop_final_contextParameters :
    StandardLattice.SiegelMassRatioCM → (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) →
    ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop),
      GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' →
      (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) →
      RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) :=
  fun hAll hU KP Q Q' QO hB hF hE hS hEv =>
    _root_.GlobalTheory.Fc.recExP_of_recAtG hAll Q' QO
      (_root_.GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes (GlobalTheory.Mem.VolMass.volumes_eq_masses_of_unfold hU) KP Q Q' hB hF hE hS)
      hEv

end GlobalTheory.Fc
