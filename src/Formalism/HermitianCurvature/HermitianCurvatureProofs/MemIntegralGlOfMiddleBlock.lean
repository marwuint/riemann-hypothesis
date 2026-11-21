import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x3

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)

section Blocks

variable {A : Type} {r k : ℕ}

@[simp] theorem block11_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b11 (x.map f) = (b11 x).map f := rfl

@[simp] theorem block12_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b12 (x.map f) = (b12 x).map f := rfl

@[simp] theorem block13_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b13 (x.map f) = (b13 x).map f := rfl

@[simp] theorem block21_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b21 (x.map f) = (b21 x).map f := rfl

@[simp] theorem block22_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b22 (x.map f) = (b22 x).map f := rfl

@[simp] theorem block23_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b23 (x.map f) = (b23 x).map f := rfl

@[simp] theorem block31_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b31 (x.map f) = (b31 x).map f := rfl

@[simp] theorem block32_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b32 (x.map f) = (b32 x).map f := rfl

@[simp] theorem block33_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b33 (x.map f) = (b33 x).map f := rfl

variable [CommRing A]

theorem block11_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b11 (x * y) = b11 x * b11 y + b12 x * b21 y + b13 x * b31 y := by
  ext i j
  simp [b11, b11, b12, b13, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block12_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b12 (x * y) = b11 x * b12 y + b12 x * b22 y + b13 x * b32 y := by
  ext i j
  simp [b12, b11, b12, b13, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block13_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b13 (x * y) = b11 x * b13 y + b12 x * b23 y + b13 x * b33 y := by
  ext i j
  simp [b13, b11, b12, b13, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block21_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b21 (x * y) = b21 x * b11 y + b22 x * b21 y + b23 x * b31 y := by
  ext i j
  simp [b21, b21, b22, b23, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block22_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b22 (x * y) = b21 x * b12 y + b22 x * b22 y + b23 x * b32 y := by
  ext i j
  simp [b22, b21, b22, b23, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block23_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b23 (x * y) = b21 x * b13 y + b22 x * b23 y + b23 x * b33 y := by
  ext i j
  simp [b23, b21, b22, b23, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block31_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x * y) = b31 x * b11 y + b32 x * b21 y + b33 x * b31 y := by
  ext i j
  simp [b31, b31, b32, b33, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block32_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b32 (x * y) = b31 x * b12 y + b32 x * b22 y + b33 x * b32 y := by
  ext i j
  simp [b32, b31, b32, b33, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block33_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b33 (x * y) = b31 x * b13 y + b32 x * b23 y + b33 x * b33 y := by
  ext i j
  simp [b33, b31, b32, b33, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

@[simp] theorem block11_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b11 (hEmb r h) = 1 := by
  ext i j
  simp [b11, hEmb, Matrix.one_apply]

@[simp] theorem block12_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b12 (hEmb r h) = 0 := by
  ext i j
  simp [b12, hEmb]

@[simp] theorem block13_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b13 (hEmb r h) = 0 := by
  ext i j
  simp [b13, hEmb]

@[simp] theorem block21_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b21 (hEmb r h) = 0 := by
  ext i j
  simp [b21, hEmb]

@[simp] theorem block22_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b22 (hEmb r h) = midEmb h := by
  ext i j
  simp [b22, hEmb]

@[simp] theorem block23_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b23 (hEmb r h) = 0 := by
  ext i j
  simp [b23, hEmb]

@[simp] theorem block31_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b31 (hEmb r h) = 0 := by
  ext i j
  simp [b31, hEmb]

@[simp] theorem block32_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b32 (hEmb r h) = 0 := by
  ext i j
  simp [b32, hEmb]

@[simp] theorem block33_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b33 (hEmb r h) = 1 := by
  ext i j
  simp [b33, hEmb, Matrix.one_apply]

@[simp] theorem block11_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b11 (x * hEmb r h) = b11 x := by
  simp [block11_mul]

@[simp] theorem block12_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b12 (x * hEmb r h) = b12 x * midEmb h := by
  simp [block12_mul]

@[simp] theorem block13_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b13 (x * hEmb r h) = b13 x := by
  simp [block13_mul]

@[simp] theorem block21_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b21 (x * hEmb r h) = b21 x := by
  simp [block21_mul]

@[simp] theorem block22_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b22 (x * hEmb r h) = b22 x * midEmb h := by
  simp [block22_mul]

@[simp] theorem block23_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b23 (x * hEmb r h) = b23 x := by
  simp [block23_mul]

@[simp] theorem block31_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b31 (x * hEmb r h) = b31 x := by
  simp [block31_mul]

@[simp] theorem block32_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b32 (x * hEmb r h) = b32 x * midEmb h := by
  simp [block32_mul]

@[simp] theorem block33_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b33 (x * hEmb r h) = b33 x := by
  simp [block33_mul]

@[simp] theorem block11_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b11 (hEmb r h * x) = b11 x := by
  simp [block11_mul]

@[simp] theorem block12_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b12 (hEmb r h * x) = b12 x := by
  simp [block12_mul]

@[simp] theorem block13_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b13 (hEmb r h * x) = b13 x := by
  simp [block13_mul]

@[simp] theorem block21_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b21 (hEmb r h * x) = midEmb h * b21 x := by
  simp [block21_mul]

@[simp] theorem block22_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b22 (hEmb r h * x) = midEmb h * b22 x := by
  simp [block22_mul]

@[simp] theorem block23_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b23 (hEmb r h * x) = midEmb h * b23 x := by
  simp [block23_mul]

@[simp] theorem block31_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b31 (hEmb r h * x) = b31 x := by
  simp [block31_mul]

@[simp] theorem block32_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b32 (hEmb r h * x) = b32 x := by
  simp [block32_mul]

@[simp] theorem block33_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b33 (hEmb r h * x) = b33 x := by
  simp [block33_mul]

end Blocks

end Formalism.FourierDecayAlt.P.S3x3

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
