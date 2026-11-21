import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles

noncomputable section

open TensorProduct Polynomial IsLocalRing

namespace GlobalTheory.Pat

namespace Det

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

def val (y : E) : A := D.D A (1 ⊗ₜ y)

def chiAt (B : Type) [CommRing B] [Algebra A B] (x : B ⊗[A] E) : B[X] :=
  D.D B[X] (X ⊗ₜ 1 - Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B B[X]) (AlgHom.id A E) x)

def IsCH : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] (x : B ⊗[A] E), Polynomial.aeval x (D.chiAt B x) = 0

def matMap (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    B ⊗[A] Matrix (Fin n) (Fin n) A →ₐ[B] Matrix (Fin n) (Fin n) B :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) ((Algebra.ofId A B).mapMatrix)
    (fun b _ => Algebra.commutes b _)

theorem matMap_tmul (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B)
    (M : Matrix (Fin n) (Fin n) A) : matMap n A B (b ⊗ₜ M) = b • M.map (algebraMap A B) := by
  have h : matMap n A B (b ⊗ₜ M) =
      algebraMap B (Matrix (Fin n) (Fin n) B) b * M.map (algebraMap A B) :=
    Algebra.TensorProduct.lift_tmul (Algebra.ofId B _) ((Algebra.ofId A B).mapMatrix)
      (fun b _ => Algebra.commutes b _) b M
  rw [h, ← Algebra.smul_def]

def mat (n : ℕ) (A : Type) [CommRing A] : Det n A (Matrix (Fin n) (Fin n) A) where
  D B _ _ := Matrix.detMonoidHom.comp (matMap n A B).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change (matMap n A B' _).det = f (matMap n A B x).det
    rw [AlgHom.map_det]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul b M =>
      rw [Algebra.TensorProduct.map_tmul, matMap_tmul, matMap_tmul]
      ext i j
      simp
  homog B _ _ b x := by
    change (matMap n A B (b • x)).det = b ^ n * (matMap n A B x).det
    rw [map_smul, Matrix.det_smul, Fintype.card_fin]

end Det

def lagIdem {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (M : E) (a : ι → R) (i : ι) : E :=
  Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j)) •
    Polynomial.aeval M (∏ j ∈ Finset.univ.erase i, (X - C (a j)))

end GlobalTheory.Pat
