import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodParOfSigOK
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalGridNodeType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSetSumApproximation

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LiftTypeDn

theorem hasTypeAt_of_approx {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (S : SPar) (ψ : GA D V → ℂ)
    (h : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ χ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S χ ∧ ∀ x ∈ C, ‖ψ x - χ x‖ < δ) :
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S ψ := by
  intro C hC δ hδ
  obtain ⟨χ, hχ, h1⟩ := h C hC (δ / 2) (by linarith)
  obtain ⟨ψ', hψ', h2⟩ := hχ C hC (δ / 2) (by linarith)
  refine ⟨ψ', hψ', fun x hx => ?_⟩
  have e : ψ x - ψ' x = (ψ x - χ x) + (χ x - ψ' x) := by ring
  rw [e]
  have := norm_add_le (ψ x - χ x) (χ x - ψ' x)
  linarith [h1 x hx, h2 x hx]

end GlobalTheory.LiftTypeDn
