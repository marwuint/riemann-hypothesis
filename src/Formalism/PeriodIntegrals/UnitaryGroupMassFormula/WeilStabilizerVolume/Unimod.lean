import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.VolStabW

open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal

section Spec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct

instance t2Space_adelic_unitary (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    T2Space (HA (AF F) σ J) := inferInstanceAs (T2Space (HR (AF F) σ J))

end Spec

end PI.VolStabW
