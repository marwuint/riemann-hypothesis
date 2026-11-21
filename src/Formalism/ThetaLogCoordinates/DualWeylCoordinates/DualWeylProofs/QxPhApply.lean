import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbIndepField

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ}

variable {M M' : GLMod n}

abbrev qx_J (Str : (Fin n → ℤ) → Finset (Fin n → ℤ)) (CF : ColFam M) : Type :=
  Σ j : CF.J, ↥(Str (CF.mu j))

def qx_ph (ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M)
    (x : qx_J Str CF) : Matrix M'.ι (TIdx (x.2 : Fin n → ℤ)) ℤ :=
  fun i I => ∑ K : TIdx (CF.mu x.1), CF.ph x.1 (e i).1 K * ps (CF.mu x.1) x.2 (K, (e i).2) I

lemma qx_ph_apply (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) (x : qx_J Str CF) (i : M'.ι)
    (I : TIdx (x.2 : Fin n → ℤ)) :
    qx_ph ps e CF x i I = ∑ K : TIdx (CF.mu x.1), CF.ph x.1 (e i).1 K * ps (CF.mu x.1) x.2 (K, (e i).2) I := rfl

end Formalism.InvariantFactorPaths.ColumnFamilies
