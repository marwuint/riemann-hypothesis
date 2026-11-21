import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.IdxCalc

noncomputable section

namespace PI.Dv.ProjAW

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Gen

variable (A : HLat K)

lemma mem_cutE (f : Module.End K A.V) (M : Submodule (𝓞 K) A.V) (x : A.V) :
    x ∈ cutE A f M ↔ x ∈ M ∧ x ∈ LinearMap.range f := Iff.rfl

lemma mem_imgE (f : Module.End K A.V) (M : Submodule (𝓞 K) A.V) (x : A.V) :
    x ∈ imgE A f M ↔ ∃ y ∈ M, f y = x := Iff.rfl

end Gen

end PI.Dv.ProjAW
