import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.ContDiffOnExpPartialHomeomorphSymm

namespace CompanionTheory.D.Upq

open Matrix

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

section Generic

variable (J : Matrix n n ℂ)

def lieJ : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | Xᴴ * J + J * X = 0}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq, conjTranspose_add, Matrix.add_mul, Matrix.mul_add] at hX hY ⊢
    calc Xᴴ * J + Yᴴ * J + (J * X + J * Y) = (Xᴴ * J + J * X) + (Yᴴ * J + J * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' r X hX := by
    simp only [Set.mem_ofPred_eq, conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul] at hX ⊢
    rw [← smul_add, hX, smul_zero]

theorem mem_lieJ {X : Matrix n n ℂ} : X ∈ lieJ J ↔ Xᴴ * J + J * X = 0 := Iff.rfl

variable {J}

theorem conjTranspose_mul_eq_of_mem {X : Matrix n n ℂ} (hX : X ∈ lieJ J) : Xᴴ * J = -(J * X) :=
  eq_neg_of_add_eq_zero_left hX

theorem commutator_mem_lieJ {X Y : Matrix n n ℂ} (hX : X ∈ lieJ J) (hY : Y ∈ lieJ J) :
    X * Y - Y * X ∈ lieJ J := by
  have hX' := conjTranspose_mul_eq_of_mem hX
  have hY' := conjTranspose_mul_eq_of_mem hY
  show (X * Y - Y * X)ᴴ * J + J * (X * Y - Y * X) = 0
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul,
    Matrix.mul_assoc Yᴴ Xᴴ J, hX', Matrix.mul_assoc Xᴴ Yᴴ J, hY', Matrix.mul_neg, Matrix.mul_neg,
    ← Matrix.mul_assoc Yᴴ J X, hY', ← Matrix.mul_assoc Xᴴ J Y, hX']
  simp only [Matrix.neg_mul, neg_neg, Matrix.mul_sub, Matrix.mul_assoc]
  abel

variable (J) in

def lieSubJ : LieSubalgebra ℝ (Matrix n n ℂ) :=
  { lieJ J with
    lie_mem' := fun {X Y} hX hY => by
      rw [Ring.lie_def]
      exact commutator_mem_lieJ hX hY }

@[simp] theorem mem_lieSubJ {X : Matrix n n ℂ} : X ∈ lieSubJ J ↔ X ∈ lieJ J := Iff.rfl

end Generic

section Involutive

variable {J : Matrix n n ℂ} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ

theorem mul_J_J (Z : Matrix n n ℂ) : Z * J * J = Z := by
  rw [Matrix.mul_assoc, hJ, Matrix.mul_one]

theorem mem_lieJ_iff {X : Matrix n n ℂ} : X ∈ lieJ J ↔ Xᴴ = -(J * X * J) := by
  constructor
  · intro h
    calc Xᴴ = Xᴴ * J * J := (mul_J_J hJ _).symm
      _ = -(J * X * J) := by rw [conjTranspose_mul_eq_of_mem h, Matrix.neg_mul]
  · intro h
    show Xᴴ * J + J * X = 0
    rw [h, Matrix.neg_mul, mul_J_J hJ, neg_add_cancel]

end Involutive

section Cartan

variable (J : Matrix n n ℂ)

def kJ : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | X ∈ lieJ J ∧ X * J = J * X}
  add_mem' {X Y} hX hY := ⟨add_mem hX.1 hY.1, by rw [Matrix.add_mul, Matrix.mul_add, hX.2, hY.2]⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  smul_mem' c X hX := ⟨Submodule.smul_mem _ c hX.1, by
    rw [Matrix.smul_mul, Matrix.mul_smul, hX.2]⟩

def pJ : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | X ∈ lieJ J ∧ X * J = -(J * X)}
  add_mem' {X Y} hX hY := ⟨add_mem hX.1 hY.1, by
    rw [Matrix.add_mul, Matrix.mul_add, hX.2, hY.2, neg_add]⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  smul_mem' c X hX := ⟨Submodule.smul_mem _ c hX.1, by
    rw [Matrix.smul_mul, Matrix.mul_smul, hX.2, smul_neg]⟩

theorem mem_kJ {X : Matrix n n ℂ} : X ∈ kJ J ↔ X ∈ lieJ J ∧ X * J = J * X := Iff.rfl

theorem mem_pJ {X : Matrix n n ℂ} : X ∈ pJ J ↔ X ∈ lieJ J ∧ X * J = -(J * X) := Iff.rfl

variable {J} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ

end Cartan

end CompanionTheory.D.Upq
