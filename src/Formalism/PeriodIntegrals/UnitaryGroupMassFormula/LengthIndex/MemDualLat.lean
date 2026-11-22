import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.IdxCalc

noncomputable section

namespace PI.Dv.ProjAW

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {K : Type} [Field K] [NumberField K]

variable [StarRing K] (A : HLat K)

lemma mem_dualLat {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (M : Submodule (𝓞 K) V) (f : Module.Dual K V) :
    f ∈ Formalism.HN.dualLat M ↔ ∀ x ∈ M, f x ∈ Set.range (algebraMap (𝓞 K) K) := Iff.rfl

end PI.Dv.ProjAW
