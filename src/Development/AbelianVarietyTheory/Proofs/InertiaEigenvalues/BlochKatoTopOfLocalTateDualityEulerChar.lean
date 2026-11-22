import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedLatticeCohomologyTheoremTOP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeOfPowMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionRuleStmt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroOfDiag
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrPartAEveryRecord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHold
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStatementHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionSaturationUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharactersGivenJumpsUnramifiedTwists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysLitAll

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TopClosing

theorem blochKatoTop_of_localTateDuality_eulerChar_alt : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), tableLineDegreeTwo.aux₃ D HW F := by
  intro _ hdual heul D HW F Cm
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, -, hE⟩ :
      Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm := _root_.GlobalTheory.NL.wach_used_clauses D HW F Cm
  obtain ⟨a23, a24⟩ := tableLineDegreeTwo.ainf_clauses_of_theorem D HW F hE
  have hA : Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F := GlobalTheory.HerrFull.herr_part_a_every_record D HW F
  have hFN : Formalism.MainNotions.HerrComplexNaturality.FN D HW F := GlobalTheory.Decompl.fontaine_and_decompletion D HW F
  have a16 : tableLineDegreeTwo.adm16 D HW F :=
    Formalism.MainNotions.InvariantsGenerators.herr_lattice_of_fon D HW F ⟨hA, _root_.GlobalTheory.invariants_of_field_of_norms D HW F hFN, _root_.GlobalTheory.fontaine_litFont_assembled D HW F⟩
  have a17 : tableLineDegreeTwo.adm17 D HW F :=
    (Formalism.MainNotions.InvariantsGenerators.herr_lattice_rest_iff D HW F).2
      ⟨GlobalTheory.EtaleSub.exists_lattice_of_pow_mem D HW F, GlobalTheory.ExtDict.extension_rule D HW F⟩
  have a21 : tableLineDegreeTwo.adm21 D HW F := GlobalTheory.SenMult.stmtSen D HW F Cm ⟨a2, a4, a5, a9, a11⟩
  exact GlobalTheory.TopBridge.twistedLatticeCohomology_theoremTOP D HW F Cm
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, ⟨hdual, heul⟩,
      GlobalTheory.FiltrationJumpMultiplicity.blochKato_dimension_saturation_unramified D, _root_.GlobalTheory.CrysCharJumps.adm20_of_fonOf D HW F, a21, GlobalTheory.CrysFormalism.crysLit_all D, a23, a24⟩

end GlobalTheory.TopClosing
