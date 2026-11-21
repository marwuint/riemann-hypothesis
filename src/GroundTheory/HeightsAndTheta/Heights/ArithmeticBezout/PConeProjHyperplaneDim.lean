import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeProjHyperplaneDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussNormEqCoeffGaussNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartGram
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre mcPts psiPoly)

namespace ConeProjHyperplaneDim

def coneForm {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    MvPolynomial (Fin n) ℂ :=
  rename (fun p : Σ k : Unit, PBlk n k => p.2) (psiPoly Ψ j)

theorem coneForm_zero {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    coneForm Ψ 0 = coneFirstForm Ψ := rfl

end ConeProjHyperplaneDim

end GroundTheory.Heights₂.Heights
