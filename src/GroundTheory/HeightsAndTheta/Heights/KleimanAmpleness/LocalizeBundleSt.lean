import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

instance LocalizeBundle.hyps : (Ideal.span {(2 : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two

abbrev LocalizeBundle.exO : Type := Localization.AtPrime (Ideal.span {(2 : ℤ)})

abbrev LocalizeBundle.exΩ : Type := FractionRing LocalizeBundle.exO

instance LocalizeBundle.exTower : @IsScalarTower ℤ LocalizeBundle.exO LocalizeBundle.exΩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
