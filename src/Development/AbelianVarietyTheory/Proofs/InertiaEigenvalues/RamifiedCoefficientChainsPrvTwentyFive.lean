import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremCHypothesesAdmitted
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremCConst25OfHypotheses
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceAdmissibleOfGapConstantLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvalueProductMapsLetterLatticeOfConclusionsA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisRest
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem ramifiedCoefficientChains_prv_twenty_five :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
        RamifiedCoefficientChains.aux₃ D HW F 25 := by
  intro hBK hTD hEC D HW F Cm
  have hadm := _root_.GlobalTheory.TheoremCAdm.admissible_ranks_of_CMDatum hBK hTD hEC D HW F Cm
  have h23 : LiftingTheory.adm23 D HW F := (GlobalTheory.jumps_exact_adm D HW F).2
  have hC4 : LetterConditionGlobal D HW F := _root_.GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions D HW F Cm (_root_.GlobalTheory.NL.wach_used_clauses D HW F Cm)
  have hH : ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F := GlobalTheory.AdmHerrLocal.main D HW F
  have h22 : CrystallineLiftingBounds.adm22 D HW F := GlobalTheory.FontaineIneq.one_place_admissible_of_gap_constant_le D HW F
  have hL : InvariantsGenerators.LitFont D HW F := _root_.GlobalTheory.fontaine_litFont_assembled D HW F
  exact _root_.GlobalTheory.theoremC_of_admitted_inputs D HW F Cm 10 23 32 32 h23 hC4 hH h22 hL hadm

end GlobalTheory
