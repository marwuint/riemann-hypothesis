import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionActionOnFixK1
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUpperMulInc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelUniqueOfIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelOfParabolicVector
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp.ParInd

section Blocks
variable {R : Type} [CommRing R] {a b : ℕ}

theorem entN_tl (M : Matrix (Fin (a + b)) (Fin (a + b)) R) (i j : Fin a) :
    entN M i j = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [entN, hi, hj, and_self, dif_pos]
  rfl

theorem entN_br (M : Matrix (Fin (a + b)) (Fin (a + b)) R) (i j : Fin b) :
    entN M (a + i) (a + j) = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [entN, hi, hj, and_self, dif_pos]
  rfl

theorem entN_self {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) : entN M i j = M i j := by
  simp [entN]

theorem det_par (M : Matrix (Fin (a + b)) (Fin (a + b)) R)
    (h : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0) :
    M.det = (Matrix.of fun i j : Fin a => entN M i j).det *
      (Matrix.of fun i j : Fin b => entN M (a + i) (a + j)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have h0 : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    apply h <;> simp
  rw [h0, Matrix.det_fromBlocks_zero₂₁]
  congr 2 <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, entN_tl, entN_br]

theorem exists_blocks (p : GL (Fin (a + b)) R)
    (h : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix _ _ R) i j = 0) :
    ∃ (x : GL (Fin a) R) (y : GL (Fin b) R),
      (∀ i j : Fin a, (x : Matrix _ _ R) i j = entN (p : Matrix (Fin (a + b)) (Fin (a + b)) R) i j) ∧
      (∀ i j : Fin b, (y : Matrix _ _ R) i j = entN (p : Matrix (Fin (a + b)) (Fin (a + b)) R) (a + i) (a + j)) := by
  have hu : IsUnit (p : Matrix (Fin (a + b)) (Fin (a + b)) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit
  rw [det_par _ h] at hu
  have h1 := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hu)
  have h2 := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hu)
  exact ⟨h1.unit, h2.unit, fun i j => by simp, fun i j => by simp⟩

def dg (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) : Matrix (Fin (a + b)) (Fin (a + b)) R :=
  fun i j => if (i : ℕ) < a ∧ (j : ℕ) < a then entN x i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then entN y (i - a) (j - a) else 0

theorem dg_par (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin (a + b))
    (hj : (j : ℕ) < a) (hi : a ≤ (i : ℕ)) : dg x y i j = 0 := by
  unfold dg
  rw [if_neg (by omega), if_neg (by omega)]

theorem dg_tl (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin a) :
    entN (dg x y) i j = x i j := by
  rw [entN_tl]
  simp [dg, entN_self]

theorem dg_br (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin b) :
    entN (dg x y) (a + i) (a + j) = y i j := by
  rw [entN_br]
  simp [dg, entN_self]

theorem dg_det (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) :
    (dg x y).det = x.det * y.det := by
  rw [det_par _ (dg_par x y)]
  congr 2 <;> ext i j <;> simp [dg_tl, dg_br]

theorem dg_unit (x : GL (Fin a) R) (y : GL (Fin b) R) : IsUnit (dg x.val y.val) := by
  rw [Matrix.isUnit_iff_isUnit_det, dg_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit)

end Blocks

variable {g : ℕ} [Fact g.Prime] {a b : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem inc_val (n : ℕ) (k : GL (Fin n) ℤ_[g]) : (inc g n k).val = k.val.map (algebraMap ℤ_[g] ℚ_[g]) := rfl

theorem red_val (n : ℕ) (k : GL (Fin n) ℤ_[g]) : (red g n k).val = k.val.map (PadicInt.toZMod (p := g)) := rfl

theorem det_inc (n : ℕ) (k : GL (Fin n) ℤ_[g]) : Matrix.GeneralLinearGroup.det (inc g n k) =
    Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, inc_val, Units.coe_map]
  exact ((algebraMap ℤ_[g] ℚ_[g]).map_det k.val).symm

variable {π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V} {σ : Representation ℂ (GL (Fin a) ℚ_[g]) W}
  {ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ} {Λ : V →ₗ[ℂ] W} {χ : (ZMod g)ˣ →* ℂˣ}

theorem blk_val (x : Gn g a) (y : Gn g b) : (blk a b (a + b) x y).val = dg x.val y.val := by
  have hu := dg_unit x y
  change (toG (dg x.val y.val)).val = _
  rw [toG, dif_pos hu, IsUnit.unit_spec]

end GlobalTheory.GLp.ParInd
