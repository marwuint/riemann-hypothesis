import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

instance LocalizeNefAbove.hyps₁ : (Ideal.span {(2 : ℤ)}).IsMaximal :=
  ((Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two).isMaximal (by simp)

abbrev LocalizeNefAbove.exO : Type := Localization.AtPrime (Ideal.span {(2 : ℤ)})

abbrev LocalizeNefAbove.exΩ : Type := FractionRing LocalizeNefAbove.exO

instance LocalizeNefAbove.exTower : @IsScalarTower ℤ LocalizeNefAbove.exO LocalizeNefAbove.exΩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
