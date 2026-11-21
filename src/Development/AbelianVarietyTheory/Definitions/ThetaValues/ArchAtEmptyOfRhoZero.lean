import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.NotJInjRdOfConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsLtMulOfLt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfB
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UnfoldPoincareOnto
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetFderivNeZeroOrbit
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KronHolPsiOf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnOfCharts
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableIndicatorOfContOn
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLtTopOfCutoff
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightContDiffOn
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.VanishOfSimpleZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfHermOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.EtaStatementHolds

noncomputable section

namespace GlobalTheory.Shares.Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.RunIn

section Poly

open MvPolynomial

variable {n : ℕ}

def ex (a : ℕ) (α : Fin n → ℕ) : Fin (n + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm (Fin.cons a α)

@[simp] theorem ex_zero (a : ℕ) (α : Fin n → ℕ) : ex a α 0 = a := rfl
@[simp] theorem ex_succ (a : ℕ) (α : Fin n → ℕ) (i : Fin n) : ex a α i.succ = α i := rfl

def supp (q : (Fin (n + 1) →₀ ℕ) → Prop) : Submodule ℂ (MvPolynomial (Fin (n + 1)) ℂ) where
  carrier := {p | ∀ β, ¬ q β → coeff β p = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun hp hq β hβ => by simp [hp β hβ, hq β hβ]
  smul_mem' := fun c p hp β hβ => by simp [hp β hβ]

end Poly

section Examples₂

open MvPolynomial

variable {D : D7} (B₀ : WeightFamilies.Prov D)

variable {B₀} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X₀ : PJ D B₀ P j) (hj : InR D j)

def fn (n : ℕ) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ((Fin n → ℂ) → ℂ) := aeval fun i y => y i

variable {K : Type} [Field K] (σ : K →+* ℂ)

end Examples₂

end GlobalTheory.Shares.Model
