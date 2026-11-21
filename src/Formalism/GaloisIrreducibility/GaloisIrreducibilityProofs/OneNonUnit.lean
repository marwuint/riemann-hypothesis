import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility
open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

@[simp] lemma zero_ne_succ' {m : ℕ} (k : Fin m) : ((0 : Fin (m+1)) = k.succ) ↔ False := ⟨fun h => Fin.succ_ne_zero k h.symm, fun h => h.elim⟩

def bord {m : ℕ} (M : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m+1)) (Fin (m+1)) R :=
  Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (M i)))

@[simp] lemma bord_zero_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) R) : bord M 0 0 = 1 := by
  simp [bord]
@[simp] lemma bord_zero_succ {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    bord M 0 j.succ = 0 := by
  simp [bord]
@[simp] lemma bord_succ_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    bord M i.succ 0 = 0 := by
  simp [bord]
@[simp] lemma bord_succ_succ {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    bord M i.succ j.succ = M i j := by
  simp [bord]

end BorderedIndexCases

open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

def Equi {s : ℕ} (A B : Matrix (Fin s) (Fin s) R) : Prop :=
  ∃ P Q : Matrix (Fin s) (Fin s) R, IsUnit P ∧ IsUnit Q ∧ P * A * Q = B

lemma Equi.trans {s : ℕ} {A B C : Matrix (Fin s) (Fin s) R} (h1 : Equi A B) (h2 : Equi B C) :
    Equi A C := by
  unfold Equi at h1 h2 ⊢
  obtain ⟨P1, Q1, hP1, hQ1, rfl⟩ := h1
  obtain ⟨P2, Q2, hP2, hQ2, rfl⟩ := h2
  exact ⟨P2 * P1, Q1 * Q2, hP2.mul hP1, hQ1.mul hQ2, by simp only [Matrix.mul_assoc]⟩

end BorderedIndexCases

open Matrix

namespace BorderedIndexCases

end BorderedIndexCases

end Formalism.GaloisIrreducibility
