import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPendingObjectsDepthZeroAdmissibleEigenSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraCentreKeepsTypeSpacesAtLocalisations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualOfLabels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfIsConjPl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicRowLocalSplitExists
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftThroughCompletionIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharOfLowerRightBlockDetEventuallyEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalIntegerCongrTameGeneratorCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharacterUnitValue
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameUniformizerPower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDZOfSplitReg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitLocalOfGreen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularLocalOfDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfJointCond
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGenAtTransport
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisDepthZeroTame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisDepthZeroEntrywise

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PinClose
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) →
    LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → SumRepresentations.tie0 D → SumRepresentations.adm5 D →
    ZLStable D → CenInt D → SerLL D → CoeffRingsHaveRootsOfUnity D → ∃ Q : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  intro hPr hSu hL D P hRow hLab hCen hGr hChi ht0 ha5 hZL hCI hSer hZ
  obtain ⟨hIne, hDep, hGen⟩ := GlobalTheory.LabTies.main D P.T hLab
  have hCT : OnMtPreservesTypeV D := _root_.GlobalTheory.CenKeepsTypeLoc.main D P.M P.H.av hCen
  have hDZ : DepthZ D := _root_.GlobalTheory.T.depthZ_of_rowMod_labAll_chiTOk hPr hSu hL D P hRow hLab hChi
  have hAdm : PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := _root_.GlobalTheory.T.admDepthZero_of_rowMod_labAll_greenLab hPr hL D P hRow hLab hCen hGr hChi
  have hPar : ∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par,
      ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w := by
    intro S
    refine ⟨P.ty.par.eP.symm ⟨S.1, S.2⟩, fun w => ?_⟩
    rw [P.ty.par.locPar_def]
    have e := P.ty.par.eP.apply_symm_apply (⟨S.1, S.2⟩ : HeightCounting.ParC D)
    rw [e]
  exact GlobalTheory.T.exists_pending_objects_depthZero_admissible_eigenSpan D P.M P.H.hecke P.H.rational P.H.av hPar ht0 ha5 hIne hDep hGen hZL hCI hCT hSer hZ hDZ hAdm
end GlobalTheory.PinClose
end
end
