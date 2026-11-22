import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LettersFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeComparisonDcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrH1Description
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemH1fIffResMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionAtLowLevelPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleSaturatedExactnessCrystalline
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocyclePolesFrobeniusQCrystalline
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionIntegralCocycleAllPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleDescentToTameSubextension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachIntegralComplexCocycleClassFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefectTorsionSecondCohomologyKernel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelCrystallineSurjectionKilledByXPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHolds

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL

theorem wach_used_clauses (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : DeltaInvariantNormBound D HW F Cm := by
  unfold DeltaInvariantNormBound
  refine ⟨GlobalTheory.NL.LetterFree.letters_free D HW F, GlobalTheory.NL.WachLatticeTrivialModUniformizer.wachLattice_galois_trivial_mod_uniformizer D HW F Cm,
    GlobalTheory.NL.CmpCris.wachLattice_comparison_dcris D HW F Cm, _root_.GlobalTheory.NL.LatLevel.lattice_at_level D HW F Cm, _root_.GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm,
    _root_.GlobalTheory.NL.Exact.exactness_of_N D HW F Cm, _root_.GlobalTheory.NL.PoleCrys.main D HW F, _root_.GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places D HW F Cm, _root_.GlobalTheory.NL.p9_statement D HW F,
    _root_.GlobalTheory.NL.FrobeniusMatrixUniqueness.main D HW F, _root_.GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient D HW F Cm, GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F,
    GlobalTheory.NL.FiniteRestrictionH1f.mem_H1f_iff_res_mem D HW F, _root_.GlobalTheory.NL.IntComplex.main D HW F, _root_.GlobalTheory.NL.DefectTorsion.defect_torsion D HW F Cm,
    _root_.GlobalTheory.NL.CokerKill.X_pow_kills_coker D HW F Cm, ?_⟩
  unfold ConclusionE
  exact ⟨GlobalTheory.NL.NygaardExtension.main D HW F, _root_.GlobalTheory.NL.SandJumps.main D HW F Cm⟩

end GlobalTheory.NL
