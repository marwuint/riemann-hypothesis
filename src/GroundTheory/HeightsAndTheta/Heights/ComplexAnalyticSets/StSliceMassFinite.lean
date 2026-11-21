import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def SliceMassFinite.Statement : Prop :=
  ∀ (n d : ℕ) (h : HermNorm n) (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin d) (Fin n) ℂ),
    I.IsPrime → linForm ℓ - 1 ∈ I → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = d →
    IsFiniteProjection I A →
      Integrable (chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)))

end

end GroundTheory.Heights₂.Heights
