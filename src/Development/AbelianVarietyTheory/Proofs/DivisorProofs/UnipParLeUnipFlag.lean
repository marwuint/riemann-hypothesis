import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainEmbZero

noncomputable section

namespace GlobalTheory.ThK.FlagPar

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

variable (σ) in

def stabCols {d r m : ℕ} (J : Matrix (Fin d) (Fin d) E) (X : Matrix (Fin d) (Fin r) (AE F E))
    (I : Matrix (Fin d) (Fin m) (AE F E)) : Subgroup (UA σ J) where
  carrier := {u | ∃ (A : GL (Fin r) (AE F E)) (D : GL (Fin m) (AE F E)), mat u * X = X * A.1 ∧
    ∀ z, ∃ a, mat u *ᵥ (I *ᵥ z) = I *ᵥ (D.1 *ᵥ z) + X *ᵥ a}
  one_mem' := ⟨1, 1, by simp [mat_one], fun z => ⟨0, by simp [mat_one]⟩⟩
  mul_mem' := by
    rintro u v ⟨A, D, h1, h2⟩ ⟨A', D', h1', h2'⟩
    refine ⟨A * A', D * D', ?_, fun z => ?_⟩
    · rw [mat_mul, Matrix.mul_assoc, h1', ← Matrix.mul_assoc, h1, Matrix.mul_assoc, Units.val_mul]
    · obtain ⟨a', ha'⟩ := h2' z
      obtain ⟨a, ha⟩ := h2 (D'.1 *ᵥ z)
      refine ⟨a + A.1 *ᵥ a', ?_⟩
      rw [mat_mul, ← Matrix.mulVec_mulVec, ha', Matrix.mulVec_add, ha, Matrix.mulVec_mulVec a' (mat u) X, h1,
        Matrix.mulVec_add, Units.val_mul, ← Matrix.mulVec_mulVec z D.1, ← Matrix.mulVec_mulVec a' X, add_assoc]
  inv_mem' := by
    rintro u ⟨A, D, h1, h2⟩
    have e : mat u⁻¹ * X = X * (A⁻¹).1 := by
      have : X = mat u * (X * (A⁻¹).1) := by
        rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      conv_lhs => rw [this, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
    refine ⟨A⁻¹, D⁻¹, e, fun z => ?_⟩
    obtain ⟨a, ha⟩ := h2 ((D⁻¹).1 *ᵥ z)
    refine ⟨-((A⁻¹).1 *ᵥ a), ?_⟩
    have h3 := congrArg (mat u⁻¹ *ᵥ ·) ha
    simp only [Matrix.mulVec_add] at h3
    rw [Matrix.mulVec_mulVec _ (mat u⁻¹) (mat u), mat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_mulVec z D.1,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_mulVec a (mat u⁻¹) X, e,
      ← Matrix.mulVec_mulVec] at h3
    rw [h3, Matrix.mulVec_neg, add_neg_cancel_right]

variable (σ) in

def unipCols {d r m : ℕ} (J : Matrix (Fin d) (Fin d) E) (X : Matrix (Fin d) (Fin r) (AE F E))
    (I : Matrix (Fin d) (Fin m) (AE F E)) : Subgroup (UA σ J) where
  carrier := {u | mat u * X = X ∧ ∀ z, ∃ a, mat u *ᵥ (I *ᵥ z) = I *ᵥ z + X *ᵥ a}
  one_mem' := ⟨by simp [mat_one], fun z => ⟨0, by simp [mat_one]⟩⟩
  mul_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, fun z => ?_⟩
    · rw [mat_mul, Matrix.mul_assoc, h1', h1]
    · obtain ⟨a', ha'⟩ := h2' z
      obtain ⟨a, ha⟩ := h2 z
      refine ⟨a + a', ?_⟩
      rw [mat_mul, ← Matrix.mulVec_mulVec, ha', Matrix.mulVec_add, ha, Matrix.mulVec_mulVec a' (mat u) X, h1,
        Matrix.mulVec_add, add_assoc]
  inv_mem' := by
    rintro u ⟨h1, h2⟩
    have e : mat u⁻¹ * X = X := by
      conv_lhs => rw [← h1, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
    refine ⟨e, fun z => ?_⟩
    obtain ⟨a, ha⟩ := h2 z
    refine ⟨-a, ?_⟩
    have h3 := congrArg (mat u⁻¹ *ᵥ ·) ha
    simp only [Matrix.mulVec_add] at h3
    rw [Matrix.mulVec_mulVec _ (mat u⁻¹) (mat u), mat_inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_mulVec a (mat u⁻¹) X, e] at h3
    rw [Matrix.mulVec_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h3.symm

variable (σ) in

def unipPar {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (i : ℕ) : Subgroup (UA σ W.J) :=
  unipCols σ W.J (incM F (flagX H' pl (i + 1))) (incM F (chainEmb H' pl i))

section Flag

variable {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))} {i : ℕ}

theorem mem_unipPar {u : UA σ W.J} : u ∈ unipPar σ W H' pl i ↔
    mat u * incM F (flagX H' pl (i + 1)) = incM F (flagX H' pl (i + 1)) ∧ ∀ z, ∃ a : Fin (i + 1) → AE F E,
      mat u *ᵥ (incM F (chainEmb H' pl i) *ᵥ z) = incM F (chainEmb H' pl i) *ᵥ z + incM F (flagX H' pl (i + 1)) *ᵥ a :=
  Iff.rfl

end Flag

end GlobalTheory.ThK.FlagPar

end
