import Mathlib

open scoped Classical BigOperators
open IsLocalRing

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeFlatSpecialisation

section Objects

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {F : Type} [Field F] [Algebra O F]

def Grass (r t : ℕ) : Type :=
  {U : Submodule (ResidueField O) (Fin (r + t) → ResidueField O) //
    Module.finrank (ResidueField O) U = t}

instance [Finite (ResidueField O)] (r t : ℕ) : Finite (Grass O r t) := by
  haveI : Finite (Submodule (ResidueField O) (Fin (r + t) → ResidueField O)) :=
    Finite.of_injective _ SetLike.coe_injective
  unfold Grass; infer_instance

instance [Finite (ResidueField O)] (r t : ℕ) : Fintype (Grass O r t) := Fintype.ofFinite _

end Objects

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeFlatSpecialisation
