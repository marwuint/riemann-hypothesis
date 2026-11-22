import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFinAtZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStabEmpty
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeriesAverageOtherPlaceType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragedAutomorphicFunctionKFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecompAtZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasCtpId
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkGeneratedCuspFormsOfType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormsOfVertexTypeZeroMemAndSmulMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragePreservesKFiniteness
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimStableSpaceMaxCompactAverages
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteReproducingFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteDecompositionAssembleRealPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section
namespace GlobalTheory.CuspKFinDecomp

theorem avg_lev : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ) (U : Subgroup (GA D N.V)), (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), ∀ k ∈ U, k ∈ GfC N.V → ∀ g, GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ (g * k) = GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ g := by
  intro D θ hθ N ψ U hψ τ e k hk hkf g
  unfold GlobalTheory.SeriesToClosure.avg
  congr 1
  funext k'
  rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc,
    hψ k hk hkf]

end GlobalTheory.CuspKFinDecomp
end
