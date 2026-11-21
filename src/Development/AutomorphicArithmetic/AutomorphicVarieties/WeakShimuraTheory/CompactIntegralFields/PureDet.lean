import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def eAB : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ixA ixB
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

private theorem cp_block {K : Type} [Field K] (X : M4 K) (h : IsBlock X) :
    X.charpoly = (X.submatrix ixA ixA).charpoly * (X.submatrix ixB ixB).charpoly := by
  have e : Matrix.reindex eAB.symm eAB.symm X =
      Matrix.fromBlocks (X.submatrix ixA ixA) (X.submatrix ixA ixB) 0 (X.submatrix ixB ixB) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · exact h (ixB i) (ixA j) (by revert i j; decide)
    · rfl
  rw [← Matrix.charpoly_reindex eAB.symm, e, Matrix.charpoly_fromBlocks_zero₂₁]

private theorem det_two {K : Type} [Field K] [IsAlgClosed K] (A : Matrix (Fin 2) (Fin 2) K) :
    ∃ a ∈ A.charpoly.roots, ∃ b ∈ A.charpoly.roots, A.det = a * b := by
  have hc : A.charpoly.roots.card = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]; simp
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 hc
  refine ⟨a, by simp [hab], b, by simp [hab], ?_⟩
  rw [Matrix.det_eq_prod_roots_charpoly, hab]; simp

