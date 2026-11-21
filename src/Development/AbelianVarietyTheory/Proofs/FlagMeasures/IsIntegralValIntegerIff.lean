import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc

noncomputable def idemPairHom {F E : Type} [Field F] [CommRing E] [Algebra F E] (p q : E)
    (h1 : p + q = 1) (h0 : p * q = 0) : F × F →ₐ[F] E :=
  AlgHom.ofLinearMap
    ((LinearMap.toSpanSingleton F E p).coprod (LinearMap.toSpanSingleton F E q))
    (by simpa using h1)
    (by
      rintro ⟨a, b⟩ ⟨c, d⟩
      simp only [Prod.mk_mul_mk, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply,
        Algebra.smul_def, map_mul]
      linear_combination
        (-(algebraMap F E a * algebraMap F E c * p) - algebraMap F E b * algebraMap F E d * q) * h1
        + (algebraMap F E a * algebraMap F E c + algebraMap F E b * algebraMap F E d
          - algebraMap F E a * algebraMap F E d - algebraMap F E b * algebraMap F E c) * h0)

theorem idemPairHom_apply {F E : Type} [Field F] [CommRing E] [Algebra F E] (p q : E)
    (h1 : p + q = 1) (h0 : p * q = 0) (y : F × F) :
    idemPairHom p q h1 h0 y = y.1 • p + y.2 • q := rfl

end GlobalTheory.SgLoc
