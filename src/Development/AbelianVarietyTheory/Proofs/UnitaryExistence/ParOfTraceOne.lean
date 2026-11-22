import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TorusAtExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SupRatioLeOfPhaseZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TorusThetaNorms
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorsLattice

noncomputable section

namespace GlobalTheory.TorusFrameRigid

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E]

structure Match (Y Y' : PT E) (ψ : Vsp Y.dim ≃ₗ[ℝ] Vsp Y'.dim) : Prop where
  lat : ∀ y, y ∈ Y.L ↔ ψ y ∈ Y'.L
  act : ∀ α y, ψ (act α y) = act α (ψ y)
  herm : (∀ u v, Hf (ψ u) (ψ v) = Hf u v) ∨ ∀ u v, Hf (ψ u) (ψ v) = conj (Hf u v)

variable {Y Y' : PT E} {ψ : Vsp Y.dim ≃ₗ[ℝ] Vsp Y'.dim}

variable [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}

open GlobalTheory.SemicharIndep

end GlobalTheory.TorusFrameRigid
