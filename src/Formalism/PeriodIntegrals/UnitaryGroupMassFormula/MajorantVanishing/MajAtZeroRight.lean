import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.HarderNarasimhan.ShiftInvariance

noncomputable section

namespace PI.Dv.ProjBW

open NumberField Formalism.HN

section Real

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem realize_apply (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (p : InfinitePlace K × ι × Fin 2) :
    Formalism.HermitianLatticesTheory.realize b X x p = if p.2.2 = 0 then (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).re
      else (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).im := rfl

end Real

section Zl

variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end Zl

end PI.Dv.ProjBW
