import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KroneckerTransposeMulVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoTheoremMatrixUnramifiedCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamBlockTriangularDiagonalBlocks
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationRestrictRationalContinuou
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationCocycleRationalContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomPeriodMatrixSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockTriangularExtensionCocycleTrivialDeRham
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionBlockPeriodMatrixSemistable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem extStep_holds : ExtStep := by
  intro l _ P AI T a b _ _ _ _ K r ρ ρ₁ ρ₂ c hρ hblk hdR h₁ h₂
  obtain ⟨K₁, hK₁, Q₁, hQ₁⟩ := h₁
  obtain ⟨K₂, hK₂, Q₂, hQ₂⟩ := h₂
  haveI := K₁.2
  haveI := K₂.2
  let K' : FinExt l := ⟨K₁.1 ⊔ K₂.1, inferInstance⟩
  have h1' : K₁.1 ≤ K'.1 := le_sup_left
  have h2' : K₂.1 ≤ K'.1 := le_sup_right
  have hK : K.1 ≤ K'.1 := hK₁.trans h1'
  let ι : ↥(GK K') →* ↥(GK K) := Subgroup.inclusion (GK_le hK)
  have hQ₁' : ∀ g : ↥(GK K'), ((ρ₁.comp ι) g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁ := fun g => hQ₁ ⟨g, GK_le h1' g.2⟩
  have hQ₂' : ∀ g : ↥(GK K'), ((ρ₂.comp ι) g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂ := fun g => hQ₂ ⟨g, GK_le h2' g.2⟩
  have hdR₂ : AdmDR P ρ₂ := (_root_.GlobalTheory.PMon.subQuot l P AI T a b K r ρ ρ₁ ρ₂ c hρ hblk hdR).2
  obtain ⟨hcr, hcc, hcoc⟩ := _root_.GlobalTheory.PMon.extCoc_rat_cont_cocycle l a b K K' hK r ρ ρ₁ ρ₂ c hρ hblk
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.PMon.hyodo_mat l P AI T (a × b) K' r (homRep (ρ₁.comp ι) (ρ₂.comp ι)) (homUnit Q₁ Q₂)
    (_root_.GlobalTheory.PMon.isRat_homRep_restrict l a b K K' hK r ρ ρ₁ ρ₂ c hρ hblk) (_root_.GlobalTheory.PMon.homUnit_period l P a b K' (ρ₁.comp ι) (ρ₂.comp ι) Q₁ Q₂ hQ₁' hQ₂')
    (extCoc (ρ₂.comp ι) (fun g => c (ι g))) hcr hcc hcoc
    (fun m => by
      obtain ⟨w, hw⟩ := _root_.GlobalTheory.PMon.extCoc_dies_in_BdR l P AI T a b K ρ ρ₁ ρ₂ c hblk hdR hdR₂ m
      exact ⟨w, fun g => hw (ι g)⟩)
  obtain ⟨Q, hQ⟩ := _root_.GlobalTheory.PMon.extPeriodMatrix l P a b K' (ρ.comp ι) (ρ₁.comp ι) (ρ₂.comp ι) (fun g => c (ι g)) (fun g => hblk (ι g))
    Q₁ Q₂ hQ₁' hQ₂' v hv
  exact ⟨K', hK, Q, fun g => hQ g⟩

end GlobalTheory.PMon
