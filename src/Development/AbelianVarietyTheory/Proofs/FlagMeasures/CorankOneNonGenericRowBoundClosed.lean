import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOnePairsNonGenericRowBoundOfRemainingPremiStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NongenericRowStatementsOfFamilyStatements
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyRowWeightSumUnfoldingIdentityProof
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOneTermsFamilyCutByDefect
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRowClose

theorem rowNGP_of_formNGVanish (hSW : PI.VolStabS.MassDataS.SWXS) (hC : StepChoiceConstantsC)
    (hP : StepPinExists) (hF : Formalism.L2.SG.NGVanish.FormNGC) (hB : StepThmBPinnedP) :
    RowNGP := by
  obtain ⟨h5, hw, h4, he⟩ := _root_.GlobalTheory.SnFamNG.leaves_of_fam _root_.GlobalTheory.SnFam.famNG_holds
  exact GlobalTheory.T.corankOnePairsNonGenericRowBound_of_remaining_premises hC hP hF hB (h5 _root_.GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof) (hw (GlobalTheory.T.familyGenericMassPositiveBounded_proof hSW))
    (h4 _root_.GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude) (he _root_.GlobalTheory.SnFam.existFam)

theorem close : PI.VolStabS.MassDataS.SWXS → StepChoiceConstantsC → StepPinExists →
    Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → RowNGP :=
  fun hSW hC hP hF hB => rowNGP_of_formNGVanish hSW hC hP hF hB

end GlobalTheory.NGRowClose
