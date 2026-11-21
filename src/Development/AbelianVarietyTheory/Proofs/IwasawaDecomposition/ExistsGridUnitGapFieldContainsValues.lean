import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaLiftGridDataUnitGapAllStates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimePosAllStates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldGridCharactersUniform
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbeddingFixedFieldOfLeComplexImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalSubfieldComplexFinitelyGenerate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

theorem exists_grid_fieldHas : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) := by
  intro cDep
  have h := StepW.and (_root_.GlobalTheory.HeightCounting.Up.nonempty_gridData_allSt cDep) _root_.GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt
  refine EvG.imp h (fun K _ _ _ _ hK => ?_)
  obtain ⟨S₁, P₁, A, S₂, a1, a2, hh⟩ := hK
  choose M hMf hM using _root_.GlobalTheory.GridField.exists_field_uniform cDep K.s.b
  choose S hSa hS using fun B₀ => _root_.GlobalTheory.finDimSubfield_finGen (M B₀) (hMf B₀)
  refine ⟨fun B f F => S₁ B f F ∪ S B, P₁, A, S₂, ?_, a2, ?_⟩
  · intro B f F z hz
    rcases Finset.mem_union.1 hz with hz | hz
    exacts [a1 B f F z hz, hSa B z hz]
  · intro B f T hO hH hP hA hk hF htriv w hw P x
    have hH' : Has₂ B (S₁ B.toPre f B.KsC) (S₂ B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) :=
      ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩
    obtain ⟨h1, h3⟩ := hh B f T hO hH' hP hA hk hF htriv w hw
    obtain ⟨G⟩ := h1 P x
    obtain ⟨G', hG'⟩ := hM B.toPre (w.st x.o.Z) rfl (h3 P x) _ x.m.z.R.toRealDat.toLevCh G
    have hle : M B.toPre ≤ B.fixedCoefficientFieldInComplex := hS B.toPre _ (fun z hz => hH.1 z (Finset.mem_union_right _ hz))
    obtain ⟨j, hj⟩ := _root_.GlobalTheory.exists_embedding_fixedField_of_le_complexImage (w.st x.o.Z) (M B.toPre) hle
    refine ⟨G', GlobalTheory.BigTop.Fun.FieldHas.map j ?_⟩
    rw [hj]; exact hG'

end GlobalTheory.HeightCounting.Up
