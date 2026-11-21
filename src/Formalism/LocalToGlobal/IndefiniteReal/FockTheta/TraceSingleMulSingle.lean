import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket

noncomputable section

open Formalism.IndefR.Datum Matrix

namespace Formalism.IndefR.Fock.Alg

open Formalism.IndefR.Fock.Sk

section CCRAlg

variable {ι X : Type} [DecidableEq ι] {Sm : Set (X → ℂ)} {aP aM : ι → (X → ℂ) → (X → ℂ)} {v : X → ℂ}

def lpow (aP : ι → (X → ℂ) → (X → ℂ)) (l : List ι) (v : X → ℂ) : X → ℂ := l.foldr (fun i g => aP i g) v

theorem opPow_eq (k : ι →₀ ℕ) : opPow aP k v = lpow aP (Finsupp.toMultiset k).toList v := rfl

theorem lpow_nil : lpow aP [] v = v := rfl

theorem lpow_cons (j : ι) (l : List ι) : lpow aP (j :: l) v = aP j (lpow aP l v) := rfl

end CCRAlg

section Mat

variable {m n : ℕ}

def tt (GS : Matrix (Fin n) (Fin n) ℂ) (GT : Matrix (Fin m) (Fin m) ℂ) (z w : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  (GS⁻¹ * wᴴ * GT * z).trace

theorem eM_eq (GS : Matrix (Fin n) (Fin n) ℂ) (GT : Matrix (Fin m) (Fin m) ℂ) (ξ : ℂ) (z w : Matrix (Fin m) (Fin n) ℂ) :
    eM GS GT ξ z w = 2 * (ξ * tt GS GT z w).re := rfl

end Mat

end Formalism.IndefR.Fock.Alg

end
