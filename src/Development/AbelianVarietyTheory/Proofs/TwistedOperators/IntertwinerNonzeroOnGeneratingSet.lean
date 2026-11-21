import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open Matrix Formalism.REAL Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.GraphIntertwiner

noncomputable def inlL (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] : H →L[ℂ] WithLp 2 (H × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H V).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H V)

noncomputable def sumL {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (a : H →L[ℂ] H) (b : V →L[ℂ] V) :
    WithLp 2 (H × V) →L[ℂ] WithLp 2 (H × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H V).symm.toContinuousLinearMap.comp
    ((a.prodMap b).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H V).toContinuousLinearMap)

theorem inlL_apply {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : H) :
    inlL H V x = WithLp.toLp 2 (x, 0) := rfl

theorem sumL_apply {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (a : H →L[ℂ] H) (b : V →L[ℂ] V)
    (z : WithLp 2 (H × V)) :
    sumL a b z = WithLp.toLp 2 (a z.ofLp.1, b z.ofLp.2) := rfl

end GlobalTheory.GraphIntertwiner
