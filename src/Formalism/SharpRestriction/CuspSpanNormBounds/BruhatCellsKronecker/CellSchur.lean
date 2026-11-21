import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S Matrix

section

variable {K : Type} [Field K] {n : ℕ}

def schExt (A : Matrix (Fin n) (Fin n) K) (c r : Fin n → K) (d : K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun a b => Fin.lastCases (motive := fun _ => K) (Fin.lastCases (motive := fun _ => K) d (fun j => r j) b)
    (fun i => Fin.lastCases (motive := fun _ => K) (c i) (fun j => A i j) b) a

@[simp] theorem schExt_cc (A : Matrix (Fin n) (Fin n) K) (c r : Fin n → K) (d : K) (i j : Fin n) :
    schExt A c r d i.castSucc j.castSucc = A i j := by simp [schExt]
@[simp] theorem schExt_cl (A : Matrix (Fin n) (Fin n) K) (c r : Fin n → K) (d : K) (i : Fin n) :
    schExt A c r d i.castSucc (Fin.last n) = c i := by simp [schExt]
@[simp] theorem schExt_lc (A : Matrix (Fin n) (Fin n) K) (c r : Fin n → K) (d : K) (j : Fin n) :
    schExt A c r d (Fin.last n) j.castSucc = r j := by simp [schExt]
@[simp] theorem schExt_ll (A : Matrix (Fin n) (Fin n) K) (c r : Fin n → K) (d : K) :
    schExt A c r d (Fin.last n) (Fin.last n) = d := by simp [schExt]

end

end Formalism.MainNotions.BridgeLemma

end
