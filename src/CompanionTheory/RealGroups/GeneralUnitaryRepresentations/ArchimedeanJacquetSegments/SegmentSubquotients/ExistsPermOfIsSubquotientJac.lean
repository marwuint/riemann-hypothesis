import Mathlib
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegTwo
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.MultOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlocksParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import GroundTheory.AutomorphicForms.FiniteLength
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import CompanionTheory.AutomorphicTheory.SegmentRepresentations.IrreducibleSegments.IsIrreduciblePiTensorSegTerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProductSingleFactorEquiv
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.Perm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entries_zero_or_d {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d)
    (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k))
    (hs : ∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (segTerm σ.ρ l i))) :
    ∀ i j, b.1 i j = 0 ∨ b.1 i j = d := by
  intro i j₀
  by_contra hc
  push Not at hc
  have h0 : 0 < b.1 i j₀ := Nat.pos_of_ne_zero hc.1
  have h1 : b.1 i j₀ < d := lt_of_le_of_ne (MultOne.entry_le b i j₀) hc.2
  obtain ⟨j₁, hj, h2⟩ := MultOne.exists_other b h1
  have hcu : IsCuspidal (segTerm σ.ρ l i) :=
    GlobalTheory.LocGL.isCuspidal_twist hσ (isSmoothChar_of_isUnram (isUnram_absPow k _))
  have hne : unipRad k (f i) ≠ ⊥ := by
    refine GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ?_
    have e0 : blk (f i) (f i ⟨j₀, ⟨0, h0⟩⟩) = j₀ := by simp [blk]
    have e1 : blk (f i) (f i ⟨j₁, ⟨0, h2⟩⟩) = j₁ := by simp [blk]
    rcases lt_or_gt_of_ne hj with hlt | hlt
    · exact ⟨_, _, e1.symm ▸ e0.symm ▸ hlt⟩
    · exact ⟨_, _, e0.symm ▸ e1.symm ▸ hlt⟩
  haveI := hcu.2 l (fun j => b.1 i j) (f i) hne
  have hirr : (piTensor fun j => (s i j).ρ).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun j => (s i j).irr)
      fun j φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (s i j).smooth (s i j).irr φ hφ
  exact jhMult_ne_zero_iff.2 (hs i) (jhMult_of_subsingleton hirr _)

end CompanionTheory.Pf1.SegRepC.Perm

end
