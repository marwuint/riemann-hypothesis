import Mathlib

open Polynomial Module

namespace GlobalTheory.SemisimpleConj

variable {K : Type} [Field K]

section
variable {M : Type} [AddCommGroup M] [Module K[X] M] [Module K M] [IsScalarTower K K[X] M]

instance finiteDimensional_submodule [FiniteDimensional K M] (S : Submodule K[X] M) :
    FiniteDimensional K S :=
  FiniteDimensional.of_injective ((S.subtype).restrictScalars K) Subtype.val_injective

end

end GlobalTheory.SemisimpleConj
