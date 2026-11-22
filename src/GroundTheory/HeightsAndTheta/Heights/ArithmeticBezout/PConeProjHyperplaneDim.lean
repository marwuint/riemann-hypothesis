import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeProjHyperplaneDim
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

end ConeProjHyperplaneDim

end GroundTheory.Heights₂.Heights
