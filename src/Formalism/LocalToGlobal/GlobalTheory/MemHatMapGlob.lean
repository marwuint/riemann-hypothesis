import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.Comp

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

def mapQ (Q : Matrix m n E) (Λ : Submodule (𝓞 E) (n → E)) : Submodule (𝓞 E) (m → E) :=
  Λ.map ((Matrix.mulVecLin Q).restrictScalars (𝓞 E))

theorem mem_mapQ (Q : Matrix m n E) (Λ : Submodule (𝓞 E) (n → E)) (y : m → E) :
    y ∈ mapQ Q Λ ↔ ∃ x ∈ Λ, Q *ᵥ x = y := Iff.rfl

end Formalism.L2.GlobalTheoryTheory.Comp

end
