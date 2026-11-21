import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets.FibreCurve

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

abbrev B1 : Unit → Type := fun _ => Fin 2

abbrev B2 : Fin 2 → Type := fun _ => Fin 2

section Curve

variable {Ω : Type} [Field Ω]

def pt (u : Ω) : (Σ k, B2 k) → Ω :=
  fun p => if p.1 = 0 then ![1, u] p.2 else ![1, u ^ 2] p.2

instance mCoordIdeal_isPrime (u : Ω) : (mCoordIdeal (pt u)).IsPrime :=
  RingHom.ker_isPrime _

def gen (u : Ω) : GenFibre (ι := B1) (ι' := B2) (blkV (Fin 2) 1) (mCoordIdeal (pt u)) :=
  Inter.genFibreOf _ _

end Curve

end GroundTheory.Heights₂.Heights.Targets.FibreCurve
