import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LocalDef

noncomputable section

namespace PositivityTheory.ThK.PT

open scoped Matrix
open GlobalTheory.WeilM

section Forms

variable {k : Type} [Field k] {K : Type} [CommRing K] [Algebra k K] {c : K →ₐ[k] K}

theorem map_mul_c {a b d : Type} [Fintype b] (A : Matrix a b K) (B : Matrix b d K) : (A * B).map c = A.map c * B.map c :=
  Matrix.map_mul (f := c.toRingHom)

theorem map_one_c {a : Type} [DecidableEq a] : (1 : Matrix a a K).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)

theorem exists_left_inv (hK : IsField K) {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (C : Matrix a b K)
    (h : ∀ t, C *ᵥ t = 0 → t = 0) : ∃ L : Matrix b a K, L * C = 1 := by
  letI := hK.toField
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot'.2 fun t ht => h t ht)
  refine ⟨LinearMap.toMatrix' g, Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg, Matrix.toLin'_one]

theorem isLagr_of_free [Invertible (2 : k)] (hK : IsField K) (hc : ∀ x, c (c x) = x) {N m : ℕ} (hN : N = 2 * m)
    {J : Matrix (Fin N) (Fin N) K} (hJ : IsSkewM c J) {Y : Matrix (Fin N) (Fin m) K} (hY : Yᵀ * J * Y.map c = 0)
    (hf : ∀ t, Y *ᵥ t = 0 → t = 0) : IsLagr c J Y := by
  obtain ⟨L, hL⟩ := exists_left_inv hK Y hf
  have cc : ∀ {a b : Type} (A : Matrix a b K), (A.map c).map c = A := fun A => Matrix.ext fun i j => hc _
  have hJ' : (J.map c)ᵀ = -J := Matrix.ext fun i j => hJ.1 i j
  have sk : ∀ {a b : Type} (A : Matrix (Fin N) a K) (B : Matrix (Fin N) b K),
      Bᵀ * J * A.map c = -((Aᵀ * J * B.map c).map c)ᵀ := fun A B => by
    rw [map_mul_c, map_mul_c, cc, Matrix.transpose_mul, Matrix.transpose_mul, hJ', Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin N) (Fin m) K, Yᵀ * J * Z.map c = 1 := ⟨(J⁻¹ * Lᵀ).map c, by
    rw [cc, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ.2, ← Matrix.transpose_mul, hL, Matrix.transpose_one]⟩
  have hZ' : Zᵀ * J * Y.map c = -1 := by rw [sk, hZ, map_one_c, Matrix.transpose_one]
  set S := Zᵀ * J * Z.map c with hS
  have hS' : (S.map c)ᵀ = -S := by rw [hS, neg_eq_iff_eq_neg.2 (sk Z Z)]
  let t : Matrix (Fin m) (Fin m) K := -(⅟(2 : k) • Sᵀ)
  have ht : t.map c = ⅟(2 : k) • S := by
    ext i j
    have : c (S j i) = -S i j := congrFun (congrFun hS' i) j
    simp [t, this]
  have a1 : ∀ A B : Matrix (Fin N) (Fin m) K, (A + B).map c = A.map c + B.map c := fun A B =>
    Matrix.map_add _ (map_add c) _ _
  have e1 : Yᵀ * J * (Z + Y * t).map c = 1 := by
    rw [a1, map_mul_c, Matrix.mul_add, hZ, ← Matrix.mul_assoc, hY, Matrix.zero_mul, add_zero]
  have e2 : (Z + Y * t)ᵀ * J * Y.map c = -1 := by rw [sk, e1, map_one_c, Matrix.transpose_one]
  have e3 : (Z + Y * t)ᵀ * J * (Z + Y * t).map c = 0 := by
    rw [a1, map_mul_c, Matrix.mul_add, ← Matrix.mul_assoc, e2, ht, Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul,
      Matrix.transpose_mul, Matrix.mul_assoc tᵀ, Matrix.mul_assoc tᵀ, hZ, ← hS]
    simp only [t, Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_one, Matrix.neg_mul,
      Matrix.one_mul]
    rw [add_assoc, ← neg_add, ← add_smul, invOf_two_add_invOf_two, one_smul, add_neg_cancel]
  set X := Z + Y * t
  have g : (Matrix.fromCols Y X)ᵀ * J * (Matrix.fromCols Y X).map c = Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.transpose_fromCols, Matrix.fromCols_map, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, hY, e1, e2, e3]
  have g' : ((Matrix.fromBlocks 0 (-1) 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      (((Matrix.fromCols Y X)ᵀ).map c * J.map c)) * Matrix.fromCols Y X = 1 := by
    have := congrArg (fun M => M.map c) g
    simp only [map_mul_c, cc] at this
    rw [Matrix.mul_assoc, this, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero c), map_one_c, Matrix.map_neg _ (map_neg c),
      map_one_c, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp
  exact ⟨hY, X, _, e3, (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp; omega))).1 g', g'⟩

end Forms

end PositivityTheory.ThK.PT
