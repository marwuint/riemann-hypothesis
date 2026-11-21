import Mathlib
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FlatZetaIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsNormInvSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

def LaurentConst (h : ℂ → ℂ) (s₀ c : ℂ) : Prop :=
  ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧ Tendsto (fun s => h s - p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 c)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable (Z : DivX D) (T : ThetaX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)

end GlobalTheory.ThetaInner

end
