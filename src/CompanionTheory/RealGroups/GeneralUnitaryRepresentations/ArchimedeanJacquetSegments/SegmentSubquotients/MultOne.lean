import Mathlib
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegTwo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlocksParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import GroundTheory.AutomorphicForms.FiniteLength
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import GroundTheory.AutomorphicForms.SmoothRepSchur
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.MultOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entry_le {d l : ℕ} (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (i j : Fin l) : b.1 i j ≤ d := by
  calc b.1 i j ≤ ∑ j, b.1 i j :=
        Finset.single_le_sum (f := b.1 i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = d := by simpa using b.2.1 i

theorem isSmooth_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isIrreducible_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    (segTerm σ.ρ l a).IsIrreducible :=
  GlobalTheory.LocGL.isIrreducible_twist σ.irr _

theorem hasFiniteLength_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    HasFiniteLength (segTerm σ.ρ l a) :=
  (⟨_, segTerm σ.ρ l a, isSmooth_segTerm σ a, isIrreducible_segTerm σ a⟩ :
    IrrRep (GL (Fin d) k)).hasFiniteLength

theorem exists_other {d l : ℕ} (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    {i j : Fin l} (h : b.1 i j < d) : ∃ j', j' ≠ j ∧ 0 < b.1 i j' := by
  by_contra hc
  push Not at hc
  have h2 := b.2.1 i
  simp only [Fintype.card_fin] at h2
  rw [Finset.sum_eq_single j (fun j' _ hj' => Nat.le_zero.1 (hc j' hj')) (by simp)] at h2
  omega

end CompanionTheory.Pf1.SegRepC.MultOne

end
