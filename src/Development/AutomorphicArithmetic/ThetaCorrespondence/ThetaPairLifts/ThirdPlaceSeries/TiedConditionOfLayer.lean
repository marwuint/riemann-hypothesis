import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneLabelsAllPlacesOfFixedAndConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGreenCuspidalLabellingSameGenerators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTypesOfTypesTrueReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvParamsOfRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesTrueLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigIdxFiniteTypesCOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadOfEigenLabeling
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SpecializationAtMemberOfLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemCoefficientFieldsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemHeckeCharacterTupleLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemParametersRegularGap
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemInertialTypesAtMember
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemExistsEigenvalueIndexLabeling
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemFrobeniusTracesAgree
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemUnramifiedComponentTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTied

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open RealOfReading
theorem isTied_of_layer_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ X : _root_.GlobalTheory.NRows.LinkedData hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a X.P ∧ HEq X.X.R t.r.z.R.toRealDat := by
  intro hP hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_character_choice_pin_at_of_third_layer hP hL) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.coefField_eq_TC_cf_at_member_of_published_inputs hP hL)
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.xiH_tupT_eq_tp_xi_of_used0_at_member hP hL) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_parameter_choice_and_lamAt_gap_at_member hP hL)
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.typesTrue_at_member_of_published_inputs hP hL) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_eigIdx_labeling_at_member hP hL)
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.nonempty_agree_realOfRead_at_member hP hL) (_root_.GlobalTheory.T.good_idempotent_reads_as_type_projector_at_member hP hL)))))))) ?_
  rintro K B f T w Z Wt p0 t nch n c ⟨⟨P, hPin⟩, hC, htup, ⟨hPar, hGap⟩, hTT, ⟨Xd, E, ⟨labPi⟩⟩, hAg, hE0⟩
  have hg : GlobalTheory.LiftRows.Given t.r.z.R.toRealDat t.r.z.F.lv2 :=
    ⟨(GlobalTheory.CoreOfWeak.core_of_weak t.r.z.R t.r.z.F t.r.z.pins.char t.exAt).1, hPar, t.r.intersectionNumber_baseChange.ok.ok2.irr,
      GlobalTheory.HeightCounting.goodTypes_of_typesTrue_real _ _ _ _ _ _ _ t.r.z.pins.char.base.lev hTT, t.r.z.pins.keep.guard, hGap⟩
  obtain ⟨ag⟩ := hAg hC Xd E labPi t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP
  obtain ⟨T0, hT0, hR⟩ := _root_.GlobalTheory.HeightCounting.Up.RealOfReading.exists_linked_data_of_agreement P (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi
    t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP) hPin.cf_eq hPin.C_eq hPin.tp_eq
    hPin.M_eq (hPin.rep_eq.trans c.row.rep_eq) ag (hE0 hC Xd E labPi t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP)
  exact ⟨T0, by rw [hT0]; exact hPin, hR⟩
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linked_data_pinned_at_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ X : _root_.GlobalTheory.NRows.LinkedData hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a X.P ∧ HEq X.X.R t.r.z.R.toRealDat := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt | exact _root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt <;> assumption)
end
end
