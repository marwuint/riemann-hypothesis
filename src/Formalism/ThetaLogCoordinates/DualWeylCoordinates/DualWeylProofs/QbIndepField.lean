import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.BCoreT
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def qb_ev (M : GLMod n) (F : Type) [CommRing F] (nu : Fin n → ℤ) (x : M.ι → F) : M.ι → GLCoord F n :=
  Matrix.mulVec ((prMu M nu).map (Int.castRingHom (GLCoord F n)))
    (Matrix.mulVec (M.A.map (mapCoord F)) (fun i => algebraMap F (GLCoord F n) (x i)))

lemma qb_ev_apply (M : GLMod n) (F : Type) [CommRing F] (nu : Fin n → ℤ) (x : M.ι → F) (i : M.ι) :
    qb_ev M F nu x i =
      ∑ k, (prMu M nu i k : GLCoord F n) * ∑ l, mapCoord F (M.A k l) * algebraMap F (GLCoord F n) (x l) := rfl

def qb_evL (M : GLMod n) (F : Type) [CommRing F] (nu : Fin n → ℤ) : (M.ι → F) →ₗ[F] (M.ι → GLCoord F n) where
  toFun := qb_ev M F nu
  map_add' x y := by
    funext i
    simp only [qb_ev_apply, Pi.add_apply, map_add, mul_add, sum_add_distrib]
  map_smul' a x := by
    funext i
    simp only [qb_ev_apply, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, mul_sum]
    rw [Algebra.smul_def, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun l _ => ?_
    ring

lemma qb_evL_apply (M : GLMod n) (F : Type) [CommRing F] (nu : Fin n → ℤ) (x : M.ι → F) :
    qb_evL M F nu x = qb_ev M F nu x := rfl

variable [NeZero n]

instance qb_fintypeStd (mu : Fin n → ℤ) : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _

abbrev qb_Idx {M : GLMod n} (CF : ColFam M) := Σ j : CF.J, {I : TIdx (CF.mu j) // StdT I}

def qb_vecF {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] (x : qb_Idx CF) : M.ι → F :=
  fun i => (CF.vec x.1 x.2.1 i : F)

lemma qb_vecF_def {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] (x : qb_Idx CF) :
    qb_vecF CF F x = fun i => (CF.vec x.1 x.2.1 i : F) := rfl

end Formalism.InvariantFactorPaths.ColumnFamilies
