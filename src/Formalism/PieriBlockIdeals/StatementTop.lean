import Formalism.PieriBlockIdeals.StatementDown
import Formalism.PieriBlockIdeals.HidaLatticeInclusionAtCoarseWeightBound

noncomputable section

namespace Formalism.CohomologicalDescent.Top

section SF09

open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

def HidaLatticeInclusionAtCoarseWeightBound : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι),
    W.Ok P → ∀ (l : ℕ) (X : HidaSetting ι P.Nr W.lam), l.Prime → ¬ IsUnit ((l : ℕ) : X.O) →
    P.lJ < (l : ℝ) → X.WInputs l (kc P) W.j W.T2 (W.iW P l) →
    X.Incl l (W.coarseWeightBound P l) ∧ X.Jmin l ≤ W.coarseWeightBound P l

end SF09

end Formalism.CohomologicalDescent.Top
