import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan.Frame

variable {n : ℕ}

theorem exists_frame (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.charpoly.Separable) :
    ∃ (P : GL (Fin n) ℂ) (l : Fin n → ℂ), Function.Injective l ∧
      A * P.val = P.val * Matrix.diagonal l := by
  classical
  have hnd : A.charpoly.roots.Nodup := Polynomial.nodup_roots hA
  have hcard : A.charpoly.roots.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcs : A.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  let e : Fin n ≃ A.charpoly.roots.toFinset := (Finset.equivFinOfCardEq hcs).symm
  let l : Fin n → ℂ := fun i => (e i : ℂ)
  have hl : Function.Injective l := fun i j h => e.injective (Subtype.ext h)
  have hroot : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' A) (l i) := fun i => by
    have h1 : l i ∈ A.charpoly.roots := Multiset.mem_toFinset.1 (e i).2
    have h2 : A.charpoly.IsRoot (l i) := Polynomial.isRoot_of_mem_roots h1
    apply Module.End.hasEigenvalue_iff_mem_spectrum.2
    rw [Matrix.spectrum_toLin']
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.2 h2
  have hv : ∀ i, ∃ v, Module.End.HasEigenvector (Matrix.toLin' A) (l i) v :=
    fun i => (hroot i).exists_hasEigenvector
  choose v hv using hv
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' _ l hl v hv
  have hu : IsUnit (Matrix.of v) := (Matrix.linearIndependent_rows_iff_isUnit).1 hli
  have hu' : IsUnit (Matrix.of v)ᵀ := by
    simpa using hu.map (Matrix.transposeRingEquiv (Fin n) ℂ).toRingHom
  obtain ⟨P, hP⟩ := hu'
  refine ⟨P, l, hl, ?_⟩
  rw [hP]
  ext a i
  have h := (hv i).apply_eq_smul
  have h' := congrFun h a
  rw [Matrix.toLin'_apply] at h'
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h'

end GlobalTheory.CompanionTheory.LocVan.Frame
end
