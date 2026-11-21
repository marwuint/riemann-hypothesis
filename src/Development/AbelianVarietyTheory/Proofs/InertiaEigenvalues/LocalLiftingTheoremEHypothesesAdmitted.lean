import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.ExtensionInvariantClause
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusions
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramified
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHoldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeCrystallineSequences
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulCocycle

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.AdmThmE

theorem admitted_all : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), WachCoordinates.admitted D HW F Cm 10 := by
  intro hBK hTD hEC D HW F Cm
  obtain ⟨hU, hE⟩ := _root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm
  obtain ⟨pL, pW, _, _, pWR, pH, pTr, _⟩ := _root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hBK hTD hEC D HW F Cm
  obtain ⟨_, hSatE, _, _, _, _, hKillE, _, hF1E, _, hF2E, hTools, hBC⟩ := _root_.GlobalTheory.ArcTools.arc_tools_from_clauses D HW F Cm
  obtain ⟨p1, _, _, _, _, _, _, p8, p9, _, _, a, _⟩ := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  have hX := GlobalTheory.HerrExtUnit.main D HW F
  exact ⟨hU, pL, pW, pWR, pH, pTr, hTools, hSatE, hF1E, hF2E, hKillE, _root_.GlobalTheory.GenCountUnram.admGenL_all D, hBC,
    GlobalTheory.HodgeCrysSeq.hodge_crystalline_sequences D, hE,
    Formalism.MainNotions.UnusedSlot35.extension_clause D HW F ⟨p1, p8, hX⟩,
    Formalism.MainNotions.UnusedSlot35.extension_invariant_clause D HW F ⟨p1, p8, p9, a, hX⟩⟩

end GlobalTheory.AdmThmE
