import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.IsMultiHomogOfIsChowForm

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

namespace GenericFibreIdeal

variable {n : ℕ}

attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev intUnits (n : ℕ) : Submonoid (MvPolynomial (Fin n) ℤ) :=
  (nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ)

instance : IsLocalization (intUnits n) (MvPolynomial (Fin n) ℚ) :=
  MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ

end GenericFibreIdeal

end ObjectsChow

end GroundTheory.Heights₂.Heights
