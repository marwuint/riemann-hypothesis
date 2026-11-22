import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpZeroMemLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroRead

theorem matrix_in_frame {k n Y A : Type} [CommRing k] [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y] [Fintype A]
    [DecidableEq A] (β : Matrix n Y k) (γ : Matrix Y n k) (h : γ * β = 1) (b : GL Y k) (σ : A ≃ Y) (e : A ≃ n)
    (X : Matrix A A k) (m : Matrix n n k)
    (hm : ((β * b.val).submatrix id fun i => σ (e.symm i)) * m =
      β * (b.val * X.submatrix σ.symm σ.symm * (b⁻¹).val) * γ * (β * b.val).submatrix id fun i => σ (e.symm i)) :
    m = X.submatrix e.symm e.symm := by
  let ρ : n ≃ Y := e.symm.trans σ
  have h1 : ((b⁻¹).val * γ) * (β * b.val) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ, h, Matrix.one_mul, Units.inv_mul]
  have h2 : β * (b.val * X.submatrix σ.symm σ.symm * (b⁻¹).val) * γ * (β * b.val) =
      β * b.val * X.submatrix σ.symm σ.symm := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc (b.val * _), ← Matrix.mul_assoc (b⁻¹).val, h1, Matrix.mul_one,
      Matrix.mul_assoc]
  have h3 : ∀ (P : Matrix n n k) (Q : Matrix n Y k), P * Q.submatrix id ρ = (P * Q).submatrix id ρ := fun _ _ => rfl
  have h4 : ∀ (P : Matrix Y n k) (Q : Matrix n Y k), P.submatrix ρ id * Q.submatrix id ρ = (P * Q).submatrix ρ ρ :=
    fun _ _ => rfl
  change (β * b.val).submatrix id ρ * m = _ * (β * b.val).submatrix id ρ at hm
  rw [h3, h2] at hm
  have h5 := congrArg (fun Z => ((b⁻¹).val * γ).submatrix ρ id * Z) hm
  try simp only at h5
  rw [← Matrix.mul_assoc, h4, h4, h1, ← Matrix.mul_assoc, h1, Matrix.submatrix_one_equiv, Matrix.one_mul, Matrix.one_mul] at h5
  rw [h5]
  ext i j
  simp [ρ]

theorem toEAf_onto (D : D7) : Function.Surjective (toEAf D) := by
  refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
  exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id

theorem finE_val {D : D7} (V : HSp D) (g : GA D V) : (Lev.finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl

theorem upperLeftBlock_apply_of_eq {κ : Type} [CommRing κ] {r n : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) κ) (i j : Fin r) :
    (upperLeftBlock hr g).val i j = g.val (Fin.castLE hr i) (Fin.castLE hr j) := by
  have hg : g ∈ blockTri (κ := κ) (blk2 r) := fun i j h => by
    have hi : i.val < r := lt_of_lt_of_le i.2 hn
    have hj : j.val < r := lt_of_lt_of_le j.2 hn
    simp [blk2, hi, hj] at h
  rw [upper_block_val_submatrix hr hg]
  rfl

end GlobalTheory.LevZeroRead
