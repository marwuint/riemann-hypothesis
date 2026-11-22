import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket

noncomputable section

open Formalism.IndefR.Datum Matrix

namespace Formalism.IndefR.Fock.Alg

open Formalism.IndefR.Fock.Sk

section CCRAlg

variable {ι X : Type} [DecidableEq ι] {Sm : Set (X → ℂ)} {aP aM : ι → (X → ℂ) → (X → ℂ)} {v : X → ℂ}

def lpow (aP : ι → (X → ℂ) → (X → ℂ)) (l : List ι) (v : X → ℂ) : X → ℂ := l.foldr (fun i g => aP i g) v

end CCRAlg

section Mat

variable {m n : ℕ}

def tt (GS : Matrix (Fin n) (Fin n) ℂ) (GT : Matrix (Fin m) (Fin m) ℂ) (z w : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  (GS⁻¹ * wᴴ * GT * z).trace

end Mat

end Formalism.IndefR.Fock.Alg

end
