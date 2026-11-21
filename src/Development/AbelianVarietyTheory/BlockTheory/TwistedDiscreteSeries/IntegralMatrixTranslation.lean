import Mathlib

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralMatrixTranslation

open Polynomial

section Defs

variable (O : Type) [CommRing O] (F : Type) [Field F] [Algebra O F]

def intGL (n : ℕ) : Subgroup (GL (Fin n) F) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap O F)).range

def IsIntMat {r n : ℕ} (u : Matrix (Fin r) (Fin n) F) : Prop :=
  ∀ a b, u a b ∈ (algebraMap O F).range

variable (R : Type) [CommRing R]

open Classical in

def phi0 (r n : ℕ) (u : Matrix (Fin r) (Fin n) F) : R :=
  if IsIntMat O F u then 1 else 0

variable {O F}

theorem isIntMat_of_mem {n : ℕ} {k : GL (Fin n) F} (hk : k ∈ intGL O F n) :
    IsIntMat O F (k : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨k₀, rfl⟩ := hk
  intro a b
  exact ⟨(k₀ : Matrix (Fin n) (Fin n) O) a b, rfl⟩

theorem IsIntMat.mul {l m n : ℕ} {u : Matrix (Fin l) (Fin m) F} {v : Matrix (Fin m) (Fin n) F}
    (hu : IsIntMat O F u) (hv : IsIntMat O F v) : IsIntMat O F (u * v) := by
  intro a b
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (hu a c) (hv c b)

theorem phiZero_left_invariant {r n : ℕ} {k : GL (Fin r) F} (hk : k ∈ intGL O F r) (u : Matrix (Fin r) (Fin n) F) :
    phi0 O F R r n ((k : Matrix (Fin r) (Fin r) F) * u) = phi0 O F R r n u := by
  have h : IsIntMat O F ((k : Matrix (Fin r) (Fin r) F) * u) ↔ IsIntMat O F u := by
    refine ⟨fun h => ?_, fun h => (isIntMat_of_mem hk).mul h⟩
    have h2 := (isIntMat_of_mem ((intGL O F r).inv_mem hk)).mul h
    rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at h2
  unfold phi0
  rw [h]

theorem phiZero_right_invariant {r n : ℕ} {k : GL (Fin n) F} (hk : k ∈ intGL O F n) (u : Matrix (Fin r) (Fin n) F) :
    phi0 O F R r n (u * (k : Matrix (Fin n) (Fin n) F)) = phi0 O F R r n u := by
  have h : IsIntMat O F (u * (k : Matrix (Fin n) (Fin n) F)) ↔ IsIntMat O F u := by
    refine ⟨fun h => ?_, fun h => h.mul (isIntMat_of_mem hk)⟩
    have h2 := h.mul (isIntMat_of_mem ((intGL O F n).inv_mem hk))
    rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at h2
  unfold phi0
  rw [h]

variable (O F)

def leftTr (r n : ℕ) (u : Matrix (Fin r) (Fin n) F) : GL (Fin r) F ⧸ intGL O F r → R :=
  Quotient.lift (fun g : GL (Fin r) F => phi0 O F R r n (((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * u))
    (fun g g' h => by
      have hk : g⁻¹ * g' ∈ intGL O F r := QuotientGroup.leftRel_apply.mp h
      have e : (g⁻¹ : GL (Fin r) F) = (g⁻¹ * g') * g'⁻¹ := by group
      show phi0 O F R r n _ = phi0 O F R r n _
      rw [e, Units.val_mul, Matrix.mul_assoc, phiZero_left_invariant R hk])

def rightTr (r n : ℕ) (u : Matrix (Fin r) (Fin n) F) : GL (Fin n) F ⧸ intGL O F n → R :=
  Quotient.lift (fun h : GL (Fin n) F => phi0 O F R r n (u * (h : Matrix (Fin n) (Fin n) F)))
    (fun g g' h => by
      have hk : g⁻¹ * g' ∈ intGL O F n := QuotientGroup.leftRel_apply.mp h
      have e : g' = g * (g⁻¹ * g') := by group
      show phi0 O F R r n _ = phi0 O F R r n _
      rw [← phiZero_right_invariant R hk (u * (g : Matrix (Fin n) (Fin n) F)), Matrix.mul_assoc, ← Units.val_mul, ← e])

theorem leftTr_mk (r n : ℕ) (u : Matrix (Fin r) (Fin n) F) (g : GL (Fin r) F) :
    leftTr O F R r n u (QuotientGroup.mk g) =
      phi0 O F R r n (((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * u) := rfl

theorem rightTr_mk (r n : ℕ) (u : Matrix (Fin r) (Fin n) F) (h : GL (Fin n) F) :
    rightTr O F R r n u (QuotientGroup.mk h) = phi0 O F R r n (u * (h : Matrix (Fin n) (Fin n) F)) := rfl

end Defs

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralMatrixTranslation
