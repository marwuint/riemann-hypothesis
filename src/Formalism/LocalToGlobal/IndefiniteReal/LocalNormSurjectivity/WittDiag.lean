import Mathlib

noncomputable section

open Matrix

namespace Formalism.IndefR.LocBrg.Witt

variable {R : Type} [CommRing R]

def blk0 {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of (Fin.cons (Fin.cons c fun _ => 0) fun i => Fin.cons 0 (M i))

@[simp] theorem corner_block_zero_zero {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) : blk0 c M 0 0 = c := rfl
@[simp] theorem corner_block_zero_succ {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    blk0 c M 0 j.succ = 0 := rfl
@[simp] theorem corner_block_succ_zero {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    blk0 c M i.succ 0 = 0 := rfl
@[simp] theorem corner_block_succ_succ {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk0 c M i.succ j.succ = M i j := rfl

section Main

variable [IsLocalRing R] (σ : R →+* R)

def gsR {n : ℕ} (u : R) (m : Fin n → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of (Fin.cons (Fin.cons 1 fun j => -(u * m j)) fun i => Fin.cons 0 ((1 : Matrix (Fin n) (Fin n) R) i))

@[simp] theorem gsR_zero_zero {n : ℕ} (u : R) (m : Fin n → R) : gsR u m 0 0 = 1 := rfl
@[simp] theorem gsR_zero_succ {n : ℕ} (u : R) (m : Fin n → R) (j : Fin n) : gsR u m 0 j.succ = -(u * m j) := rfl
@[simp] theorem gsR_succ_zero {n : ℕ} (u : R) (m : Fin n → R) (i : Fin n) : gsR u m i.succ 0 = 0 := rfl
@[simp] theorem gsR_succ_succ {n : ℕ} (u : R) (m : Fin n → R) (i j : Fin n) :
    gsR u m i.succ j.succ = (1 : Matrix (Fin n) (Fin n) R) i j := rfl

end Main

end Formalism.IndefR.LocBrg.Witt
