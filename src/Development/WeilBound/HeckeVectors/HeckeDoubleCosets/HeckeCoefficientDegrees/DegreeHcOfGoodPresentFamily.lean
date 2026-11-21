import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFormalDegree.VUnitInvVal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.PeriodIntegrals.UpqRep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.PeriodIntegrals.KFinSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsAuxiliaryXi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.SchurH
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.FromDS
import CompanionTheory.AutomorphicTheory.RankOneEstimates.DecSender

noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.D.Upq.Coef

section UJ

open ReciprocityTheory.ChartRestriction.DS

theorem fdeg_gap (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (h : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      120 * (n : ℝ) ^ 3 ≤ h → 1 ≤ pOf ε → 1 ≤ qOf ε → v ≠ 0 →
      Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) σ v = c * Formalism.QuantumDeterminants.fdegHC lam := by
  obtain ⟨c, hc, hH⟩ := fdCons_muG n ε
  refine ⟨c, hc, fun lam h H _ _ _ σ v hl hσ hgap hh hp hq hv => ?_⟩
  have hn : 1 ≤ n := hp.trans ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n))
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
  have ht := thrStar_le hn ε
  refine hH lam H σ v hl hσ h hgap (by linarith) hp hq (fun μ hμ hg => ?_) hv
  have hq0 : 1 ≤ S7.q0 ε := by unfold S7.q0; omega
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ thrStar ε :=
      le_max_right _ _
    have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    linarith
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ
  obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor S7.psiExists T hμ hg hq0 h8
  exact ⟨T, Ψ, hP⟩

end UJ

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] [CompleteSpace Wp] [CompleteSpace Wq]

end CompanionTheory.D.Upq.Coef

end
