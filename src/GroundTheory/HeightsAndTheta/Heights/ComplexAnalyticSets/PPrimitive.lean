import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericPrimitive
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscrAdjoin

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n d : ℕ}

def funField (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] : Type :=
  FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)

instance (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] : Field (funField J) :=
  inferInstanceAs (Field (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)))

instance (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    Algebra (MvPolynomial (Fin n) ℂ ⧸ J) (funField J) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)))

instance (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    IsFractionRing (MvPolynomial (Fin n) ℂ ⧸ J) (funField J) :=
  inferInstanceAs (IsFractionRing (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)))

end

end GroundTheory.Heights₂.Heights.ComplexSets
