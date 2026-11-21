import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomTw
import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB

open Matrix MeasureTheory

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.FrameBoundFromBesselTorus

variable {k r : ℕ}

def cjX (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  twT k r * X * twTi k r

theorem cjX_smul (c : ℂ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : cjX (c • X) = c • cjX (k := k) (r := r) X := by
  unfold cjX; rw [Matrix.mul_smul, Matrix.smul_mul]

theorem cjX_add (X Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : cjX (X + Y) = cjX (k := k) (r := r) X + cjX Y := by
  unfold cjX; rw [Matrix.mul_add, Matrix.add_mul]

def cjXI (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  twTi k r * X * twT k r

theorem realifyFun_add (X Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    realifyFun (X + Y) = realifyFun X + realifyFun Y := by
  funext p; rcases p with ⟨i, j, b⟩; cases b <;> simp [realifyFun]

theorem realifyFun_smul (c : ℝ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    realifyFun ((c : ℂ) • X) = c • realifyFun X := by
  funext p; rcases p with ⟨i, j, b⟩; cases b <;> simp [realifyFun]

def rotE (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hadd : ∀ X Y, f (X + Y) = f X + f Y) (hsm : ∀ (c : ℂ) X, f (c • X) = c • f X) :
    EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) where
  toFun y := WithLp.toLp 2 (realifyFun (f (unrealify y)))
  map_add' x y := by
    rw [unrealify_add', hadd, realifyFun_add]; rfl
  map_smul' c x := by
    rw [unrealify_smul', hsm, realifyFun_smul]; rfl

def rotC (k r : ℕ) : EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) :=
  rotE (k := k) (r := r) cjX cjX_add cjX_smul

def rotCI (k r : ℕ) : EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) :=
  rotE (k := k) (r := r) cjXI
    (fun X Y => by unfold cjXI; rw [Matrix.mul_add, Matrix.add_mul])
    (fun c X => by unfold cjXI; rw [Matrix.mul_smul, Matrix.smul_mul])

theorem rotC_apply (y : EuclideanSpace ℝ (IxE k r)) : rotC k r y = WithLp.toLp 2 (realifyFun (cjX (unrealify y))) := rfl

theorem rotCI_apply (y : EuclideanSpace ℝ (IxE k r)) :
    rotCI k r y = WithLp.toLp 2 (realifyFun (cjXI (unrealify y))) := rfl

end Formalism.MainNotions.S.Pv.Mom
