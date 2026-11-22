import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne

noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal

section One

variable {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

abbrev re : MM P Q ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ := Matrix.reindexAlgEquiv ℂ ℂ e

theorem re_star (X : MM P Q) : re e Xᴴ = (re e X)ᴴ := by
  simp [re, Matrix.reindexAlgEquiv_apply, Matrix.conjTranspose_reindex]

include h1 h2 in
theorem re_J : re e (Formalism.UG.Jpq P Q) = Jm ε := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp only [re, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Jm, Matrix.diagonal_apply, e.injective.eq_iff, Formalism.UG.Jpq]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, h1, h2] <;> split_ifs <;> simp

include h1 h2 in
theorem re_mem (M : MM P Q) : inUJ ε (re e M) ↔ Mᴴ * Formalism.UG.Jpq P Q * M = Formalism.UG.Jpq P Q := by
  unfold inUJ
  rw [← re_J ε e h1 h2, ← re_star, ← map_mul, ← map_mul]
  exact (re e).injective.eq_iff

def ofMatJ (h : Matrix (Fin n) (Fin n) ℂ) (hh : inUJ ε h) : UJ ε :=
  ⟨⟨h, Jm ε * hᴴ * Jm ε, mul_eq_one_comm.mp (coeMatrix_left_inv ε h hh), coeMatrix_left_inv ε h hh⟩, hh⟩

def ofMatU (h : MM P Q) (hh : hᴴ * Formalism.UG.Jpq P Q * h = Formalism.UG.Jpq P Q) : UpqT P Q :=
  (exists_of_mem P Q h hh).choose

theorem mat_ofMatU (h : MM P Q) (hh : hᴴ * Formalism.UG.Jpq P Q * h = Formalism.UG.Jpq P Q) :
    UpqT.mat (ofMatU h hh) = h := (exists_of_mem P Q h hh).choose_spec

include h1 h2 in
theorem symm_mem (a : UJ ε) : ((re e).symm (coeMatrixAlt ε a))ᴴ * Formalism.UG.Jpq P Q * (re e).symm (coeMatrixAlt ε a) =
    Formalism.UG.Jpq P Q :=
  (re_mem ε e h1 h2 _).mp (by rw [AlgEquiv.apply_symm_apply]; exact a.2)

def phi : UpqT P Q ≃* UJ ε where
  toFun g := ofMatJ ε (re e (UpqT.mat g)) ((re_mem ε e h1 h2 _).mpr (mat_mem P Q g))
  invFun a := ofMatU ((re e).symm (coeMatrixAlt ε a)) (symm_mem ε e h1 h2 a)
  left_inv g := mat_injective P Q (by
    rw [mat_ofMatU]
    exact (re e).symm_apply_apply _)
  right_inv a := Subtype.ext (Units.ext
    ((congrArg (re e) (mat_ofMatU _ (symm_mem ε e h1 h2 a))).trans
      ((re e).apply_symm_apply _)))
  map_mul' g g' := Subtype.ext (Units.ext (map_mul (re e) _ _))

theorem coe_phi (g : UpqT P Q) : coeMatrixAlt ε (phi ε e h1 h2 g) = Matrix.reindex e e (UpqT.mat g) := rfl

theorem phi_cont : Continuous (phi ε e h1 h2) := by
  rw [(isInducing_coeMatrix ε).continuous_iff]
  have h : coeMatrixAlt ε ∘ (phi ε e h1 h2) = fun g => (UpqT.mat g).submatrix e.symm e.symm := by
    funext g
    rw [Function.comp_apply, coe_phi, Matrix.reindex_apply]
  rw [h]
  exact (mat_cont P Q).matrix_submatrix _ _

def TR (P Q : ℕ) (R : ℝ) : Set (UpqT P Q) := {g | ∑ i, ∑ j, ‖UpqT.mat g i j‖ ^ 2 ≤ R}

theorem preimage_ball (R : ℝ) : (phi ε e h1 h2) ⁻¹' {a | hsG a ≤ R} = TR P Q R := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq, TR]
  have h : hsG (phi ε e h1 h2 g) = ∑ i, ∑ j, ‖UpqT.mat g i j‖ ^ 2 := by
    show hs (coeMatrixAlt ε (phi ε e h1 h2 g)) = _
    rw [coe_phi, hs]
    refine (Fintype.sum_equiv e.symm _ _ fun i => ?_)
    exact Fintype.sum_equiv e.symm _ _ fun j => by simp [Matrix.reindex_apply]
  rw [h]

end One

def rad (n : ℕ) : ℝ := hs (1 : Matrix (Fin n) (Fin n) ℂ) + 1

def nT {n : ℕ} (ε : Fin n → Bool) : ℕ := Fintype.card {i // ε i = true}
def nF {n : ℕ} (ε : Fin n → Bool) : ℕ := Fintype.card {i // ¬ ε i = true}

def e0 {n : ℕ} (ε : Fin n → Bool) : Fin (nT ε) ⊕ Fin (nF ε) ≃ Fin n :=
  (Equiv.sumCongr (Fintype.equivFin {i // ε i = true}).symm
    (Fintype.equivFin {i // ¬ ε i = true}).symm).trans (Equiv.sumCompl fun i => ε i = true)

theorem sign_split_equiv_inl {n : ℕ} (ε : Fin n → Bool) (i) : ε (e0 ε (Sum.inl i)) = true := by
  simp only [e0, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFin {i // ε i = true}).symm i).2

theorem sign_split_equiv_inr {n : ℕ} (ε : Fin n → Bool) (j) : ε (e0 ε (Sum.inr j)) = false := by
  show ε (((Fintype.equivFin {i // ¬ ε i = true}).symm j : {i // ¬ ε i = true}) : Fin n) = false
  simpa using ((Fintype.equivFin {i // ¬ ε i = true}).symm j).2

variable (C : CDHaar)

def cdScaleOf (n : ℕ) (ε : Fin n → Bool) : ℝ≥0 :=
  (C.cd (nT ε) (nF ε) (TR (nT ε) (nF ε) (rad n)) / muG ε {a | hsG a ≤ rad n}).toNNReal

end Formalism.BasicNotions.Examples₂.CD
