import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfLocalFilteredHypotheses
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBHypothesesAdmitted
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceAdmissibleOfGapConstantLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvalueProductMapsLetterLatticeOfConclusionsA
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem theoremB_closing : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, (320 : ℝ) ≤ C → ArcLiftingSetup.aux₃ D HW F C := by
  intro hBK hTD hEC D HW F Cm C hC
  have h22 : CrystallineLiftingBounds.adm22 D HW F := GlobalTheory.FontaineIneq.one_place_admissible_of_gap_constant_le D HW F
  have h23 : CrystallineLiftingBounds.adm23 D HW F := (GlobalTheory.jumps_exact_adm D HW F).1
  have hN1 : Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm := _root_.GlobalTheory.NL.wach_used_clauses D HW F Cm
  have hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F := _root_.GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions D HW F Cm hN1
  exact _root_.GlobalTheory.theoremB_of_admitted_inputs D HW F Cm C 10 23 32 32 8 hC h22 h23 hC4 (_root_.GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum hBK hTD hEC D HW F Cm)

end GlobalTheory
