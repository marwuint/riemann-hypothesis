import Mathlib

import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.IsHermitianForExH

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace IsoFrames

namespace Chart

open Matrix TensorProduct GroundTheory.Automorphic

noncomputable section

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

local infixl:70 " ⬝ " => @HMul.hMul _ _ _ instHMulOfFintypeOfMulOfAddCommMonoid

variable (K E R) in

def cT {m n : Type*} (M : Matrix m n (R ⊗[K] E)) : Matrix n m (R ⊗[K] E) := Matrix.transpose (M.map (conjBase K E R))

theorem conjBase_conjBase (z : (R ⊗[K] E)) : conjBase K E R (conjBase K E R z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [conjBase_tmul, conj_conj]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem conjBase_smul (c : K) (z : (R ⊗[K] E)) : conjBase K E R (c • z) = c • conjBase K E R z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [conjBase_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem cT_cT {m n : Type*} (M : Matrix m n (R ⊗[K] E)) : cT K E R (cT K E R M) = M := by
  ext i j
  simp [cT, conjBase_conjBase]

theorem cT_mul {l m n : Type*} [Fintype m] (M : Matrix l m (R ⊗[K] E)) (N : Matrix m n (R ⊗[K] E)) :
    cT K E R (M * N) = cT K E R N * cT K E R M := by
  rw [cT, cT, cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {m : Type*} [DecidableEq m] : cT K E R (1 : Matrix m m (R ⊗[K] E)) = 1 := by
  rw [cT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

variable (K R) in

def Hm (H : Matrix ι ι E) : Matrix ι ι (R ⊗[K] E) :=
  H.map (Algebra.TensorProduct.includeRight : E →ₐ[K] (R ⊗[K] E))

theorem framePair_eq (H : Matrix ι ι E) {q : ℕ} (X : Matrix ι (Fin p) (R ⊗[K] E))
    (Y : Matrix ι (Fin q) (R ⊗[K] E)) :
    framePair K E R H X Y = cT K E R X ⬝ Hm K R H ⬝ Y := rfl

theorem cT_Hm {H : Matrix ι ι E} (hH : IsHermitianFor (conjHom K E) H) :
    cT K E R (Hm K R H) = Hm K R H := by
  ext i j
  have := congrFun (congrFun hH i) j
  simp only [Matrix.transpose_apply, Matrix.map_apply] at this
  simp only [cT, Hm, Matrix.transpose_apply, Matrix.map_apply,
    Algebra.TensorProduct.includeRight_apply, conjBase_tmul]
  rw [← this]
  rfl

variable {H : Matrix ι ι E}

theorem cT_framePair (hH : IsHermitianFor (conjHom K E) H) {q : ℕ} (X : Matrix ι (Fin p) (R ⊗[K] E))
    (Y : Matrix ι (Fin q) (R ⊗[K] E)) : cT K E R (framePair K E R H X Y) = framePair K E R H Y X := by
  rw [framePair_eq, framePair_eq, cT_mul, cT_mul, cT_cT, cT_Hm hH, Matrix.mul_assoc]

def shiftT (Z X : Matrix ι (Fin p) (R ⊗[K] E)) (S : Matrix (Fin p) (Fin p) (R ⊗[K] E)) : Matrix (Fin p) (Fin p) (R ⊗[K] E) :=
  (cT K E R (framePair K E R H Z X))⁻¹ * ((2 : K)⁻¹ • S)

end

end Chart

end IsoFrames

end GroundTheory.Heights₂.Theta
