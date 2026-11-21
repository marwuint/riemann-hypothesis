import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial NumbersDVR

noncomputable section

namespace ConjIntNum

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F]

def quotEquiv (τ : F ≃+* F) (J : Ideal (MRing ι F)) :
    (MRing ι F ⧸ J) ≃+* (MRing ι F ⧸ J.map (MvPolynomial.map (τ : F →+* F))) :=
  Ideal.quotientEquiv J _ (MvPolynomial.mapEquiv _ τ) (by
    congr 1)

omit [DecidableEq K] in
theorem quotEquiv_mk (τ : F ≃+* F) (J : Ideal (MRing ι F)) (f : MRing ι F) :
    quotEquiv τ J (Ideal.Quotient.mk J f) = Ideal.Quotient.mk _ (MvPolynomial.map (τ : F →+* F) f) :=
  rfl

end ConjIntNum

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
