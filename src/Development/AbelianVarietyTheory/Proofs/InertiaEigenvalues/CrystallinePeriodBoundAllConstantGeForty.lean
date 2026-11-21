import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfLiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingStepTheoremTOfBhattScholzeFontaine
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingAdmittedHypothesesAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeCoefficientsOfPadicIntLattices

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem GlobalTheory.InertiaEigenvalues.theoremT_all_records :
    GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris → GlobalTheory.Published.BlochKatoLocal →
    Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ C : ℕ, 40 ≤ C → ElementDenominator.Conclusion2 D C := by
  intro hBS hFon hBK hTD hEC D HW F Cm C hC
  exact _root_.GlobalTheory.TheoremTClosing.main (_root_.GlobalTheory.bhattScholze_coeff hBS) hFon C hC D HW F (_root_.GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt hBK hTD hEC D HW F Cm)
