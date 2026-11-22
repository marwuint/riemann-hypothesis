import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.DoubledPlaneEmb
open Matrix

section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n n₁ : ℕ}

def coef (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (ι : Matrix (Fin n) (Fin n₁) E) :
    Matrix (Fin n₁) (Fin n) E :=
  J₁ᵀ⁻¹ * (ι.map σ)ᵀ * Jᵀ

def pairVec (J : Matrix (Fin n) (Fin n) E) (v : Fin n → E) : Fin n → E := J *ᵥ fun i => σ (v i)

def frameT (ι : Matrix (Fin n) (Fin n₁) E) (x y : Fin n → E) : Matrix (Fin n) (Fin n₁ ⊕ Fin 2) E :=
  Matrix.fromCols ι (Matrix.of fun i k => ![x i, y i] k)

def frameS (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (x y : Fin n → E) : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E :=
  Matrix.fromRows (coef σ J J₁ ι) (Matrix.of ![pairVec σ J y, pairVec σ J x])

variable {σ}

theorem form_symm {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j)
    (a b : Fin n → E) : form σ J a b = σ (form σ J b a) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ j i]; ring

end Alg

section Frame
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {ι : Matrix (Fin n) (Fin n₁) E} {x y : Fin n → E}

theorem form_col (v : Fin n → E) (k : Fin n₁) :
    form σ J v (ι *ᵥ Pi.single k 1) = ((ι.map σ)ᵀ *ᵥ (Jᵀ *ᵥ v)) k := by
  simp only [form, dotProduct, mulVec, Matrix.map_apply, transpose_apply, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Frame

section Frame2
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {ι : Matrix (Fin n) (Fin n₁) E} {x y : Fin n → E}

theorem frame_gram (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j)
    (xx : form σ J x x = 0) (yy : form σ J y y = 0) (xy : form σ J x y = 1)
    (orth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (gram : ιᵀ * J * ι.map σ = J₁) :
    (frameT ι x y)ᵀ * J * (frameT ι x y).map σ = fromBlocks J₁ 0 0 !![0, 1; 1, 0] := by
  have yx : form σ J y x = 1 := by rw [form_symm hσ hJ, xy, map_one]
  have o1 : ∀ k, form σ J x (ι *ᵥ Pi.single k 1) = 0 := fun k => by rw [form_symm hσ hJ, (orth _).1, map_zero]
  have o2 : ∀ k, form σ J y (ι *ᵥ Pi.single k 1) = 0 := fun k => by rw [form_symm hσ hJ, (orth _).2, map_zero]
  rw [frameT, transpose_fromCols, fromRows_mul, fromCols_map, fromRows_mul_fromCols, gram]
  congr 1
  · ext k r; fin_cases r
    · have := (orth (Pi.single k 1)).1
      simp [form, mul_apply, mulVec, dotProduct, Pi.single_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
    · have := (orth (Pi.single k 1)).2
      simp [form, mul_apply, mulVec, dotProduct, Pi.single_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
  · ext r k; fin_cases r
    · have := o1 k
      simp [form, mul_apply, mulVec, dotProduct, Pi.single_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
    · have := o2 k
      simp [form, mul_apply, mulVec, dotProduct, Pi.single_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
  · ext r k; fin_cases r <;> fin_cases k
    · have := xx
      simp [form, mul_apply, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
    · have := xy
      simp [form, mul_apply, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
    · have := yx
      simp [form, mul_apply, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
    · have := yy
      simp [form, mul_apply, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)

end Frame2

section Rot
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n n₁ : ℕ}

theorem fromBlocks_mul_fromRows' {R : Type} [CommRing R] {l m₁ m₂ k₁ k₂ : Type} [Fintype k₁] [Fintype k₂]
    (A : Matrix m₁ k₁ R) (B : Matrix m₁ k₂ R) (C : Matrix m₂ k₁ R) (D : Matrix m₂ k₂ R) (P : Matrix k₁ l R)
    (Q : Matrix k₂ l R) : fromBlocks A B C D * fromRows P Q = fromRows (A * P + B * Q) (C * P + D * Q) := by
  ext (i | i) j <;> simp [mul_apply, Fintype.sum_sum_type]

variable (n₁) in

def rotC : Matrix ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) E :=
  fromBlocks (fromBlocks 1 0 0 !![2⁻¹, 0; 0, 1]) (fromBlocks 0 0 0 !![2⁻¹, 0; 0, -1])
    (fromBlocks 0 0 0 !![0, 2⁻¹; -1, 0]) (fromBlocks 1 0 0 !![0, 2⁻¹; 1, 0])

variable (n₁) in

def rotCinv : Matrix ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) E :=
  fromBlocks (fromBlocks 1 0 0 !![1, 0; 0, 2⁻¹]) (fromBlocks 0 0 0 !![0, -2⁻¹; 1, 0])
    (fromBlocks 0 0 0 !![1, 0; 0, -2⁻¹]) (fromBlocks 1 0 0 !![0, 2⁻¹; 1, 0])

end Rot

section RotG
variable {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {ι : Matrix (Fin n) (Fin n₁) E} {x y : Fin n → E}

variable (σ J J₁ ι x y) in

def rotG : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E :=
  (Matrix.fromBlocks (frameT ι x y) (0 : Matrix (Fin n) (Fin n₁ ⊕ Fin 2) E) 0 (frameT ι x y) :
      Matrix (Fin n ⊕ Fin n) ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) E) * (rotC n₁ : Matrix _ _ E) *
    (Matrix.fromBlocks (frameS σ J J₁ ι x y) (0 : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E) 0 (frameS σ J J₁ ι x y) :
      Matrix ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) (Fin n ⊕ Fin n) E)

end RotG

section Ext
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {c : A →ₐ[R] A} {m k : Type} [Fintype m] [DecidableEq m]
  [Fintype k] [DecidableEq k] {K : Matrix m m A} {K₁ : Matrix k k A} {ι : Matrix m k A} {Q : Matrix k m A}

def extM (ι : Matrix m k A) (Q : Matrix k m A) (g : Matrix k k A) : Matrix m m A := 1 - ι * Q + ι * g * Q

theorem extM_one : extM ι Q 1 = 1 := by simp [extM]

theorem extM_mul (hQ : Q * ι = 1) (g h : Matrix k k A) : extM ι Q g * extM ι Q h = extM ι Q (g * h) := by
  have e1 : ∀ X : Matrix k m A, Q * (ι * X) = X := fun X => by rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  simp only [extM, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, e1]
  abel

theorem map_mul_c {a b d : Type} [Fintype b] (M : Matrix a b A) (N : Matrix b d A) :
    (M * N).map c = M.map c * N.map c := Matrix.map_mul (f := (c : A →+* A))

theorem map_add_c {a b : Type} (M N : Matrix a b A) : (M + N).map c = M.map c + N.map c := by ext; simp

theorem map_sub_c {a b : Type} (M N : Matrix a b A) : (M - N).map c = M.map c - N.map c := by ext; simp

theorem map_one_c : (1 : Matrix m m A).map c = 1 := by
  ext i j; by_cases h : i = j <;> simp [one_apply, h]

theorem extM_form (hQ : Q * ι = 1) (h2 : Qᵀ * K₁ = K * ι.map c) (h3 : ιᵀ * K = K₁ * Q.map c) (g : Matrix k k A) :
    (extM ι Q g)ᵀ * K * (extM ι Q g).map c =
      (1 - ι * Q)ᵀ * K * (1 - ι * Q).map c + Qᵀ * (gᵀ * K₁ * g.map c) * Q.map c := by
  have hιι : ιᵀ * K * ι.map c = K₁ := by
    rw [h3, Matrix.mul_assoc, ← map_mul_c, hQ, map_one_c, Matrix.mul_one]
  have hP1 : (1 - ι * Q)ᵀ * K * ι.map c = 0 := by
    rw [transpose_sub, transpose_one, transpose_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc Qᵀ,
      Matrix.mul_assoc Qᵀ, hιι, h2, sub_self]
  have hP2 : ιᵀ * K * (1 - ι * Q).map c = 0 := by
    rw [map_sub_c, map_one_c, map_mul_c, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hιι, h3, sub_self]
  have e : extM ι Q g = (1 - ι * Q) + ι * (g * Q) := by rw [extM, Matrix.mul_assoc]
  rw [e, transpose_add, map_add_c, map_mul_c, map_mul_c, transpose_mul, transpose_mul]
  have hP1' : ∀ X : Matrix k m A, (1 - ι * Q)ᵀ * (K * (ι.map c * X)) = 0 := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1, Matrix.zero_mul]
  have hP2' : ∀ {a : Type} (X : Matrix a k A), X * (ιᵀ * (K * (1 - ι * Q).map c)) = 0 := fun X => by
    rw [← Matrix.mul_assoc ιᵀ, hP2, Matrix.mul_zero]
  have hιι' : ∀ {a : Type} (X : Matrix a k A) (Y : Matrix k m A), X * (ιᵀ * (K * (ι.map c * Y))) = X * (K₁ * Y) :=
    fun X Y => by rw [← Matrix.mul_assoc K, ← Matrix.mul_assoc ιᵀ (K * ι.map c), ← Matrix.mul_assoc ιᵀ K, hιι]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hP1', hP2', hιι', add_zero, zero_add, Matrix.mul_zero]

theorem extM_unitary (hQ : Q * ι = 1) (h2 : Qᵀ * K₁ = K * ι.map c) (h3 : ιᵀ * K = K₁ * Q.map c) (g : Matrix k k A)
    (hg : gᵀ * K₁ * g.map c = K₁) : (extM ι Q g)ᵀ * K * (extM ι Q g).map c = K := by
  have h1 := extM_form hQ h2 h3 1
  simp only [extM_one, transpose_one, Matrix.one_mul, Matrix.mul_one, map_one_c] at h1
  rw [extM_form hQ h2 h3, hg]; exact h1.symm

variable (c K K₁ ι Q) in

def extHom (hQ : Q * ι = 1) (h2 : Qᵀ * K₁ = K * ι.map c) (h3 : ιᵀ * K = K₁ * Q.map c) : UG c K₁ →* UG c K where
  toFun g := ⟨⟨extM ι Q g.1.1, extM ι Q (g.1⁻¹ : GL k A).1, by rw [extM_mul hQ, Units.mul_inv, extM_one],
    by rw [extM_mul hQ, Units.inv_mul, extM_one]⟩, extM_unitary hQ h2 h3 _ g.2⟩
  map_one' := by ext1; ext1; simp [extM_one]
  map_mul' g h := by ext1; ext1; simp [extM_mul hQ]

end Ext

section ExtMore
variable {A : Type} [CommRing A] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
  {ι : Matrix m k A} {Q : Matrix k m A}

theorem det_extM (hQ : Q * ι = 1) (t : Matrix k k A) : (extM ι Q t).det = t.det := by
  have e : extM ι Q t = 1 + ι * ((t - 1) * Q) := by
    simp only [extM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]; abel
  rw [e, det_one_add_mul_comm, Matrix.mul_assoc, hQ, Matrix.mul_one, add_sub_cancel]

end ExtMore

section UaFacts
variable {A : Type} [CommRing A] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
  {ι : Matrix m k A} {Q : Matrix k m A}

end UaFacts

section More
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {ι : Matrix (Fin n) (Fin n₁) E}

end More

section Adelic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_mul' {a b d : Type} [Fintype b] (M : Matrix a b E) (N : Matrix b d E) :
    incM F (M * N) = incM F M * incM F N := Matrix.map_mul (f := inclR (F := F) (AF F))

theorem incM_add' {a b : Type} (M N : Matrix a b E) : incM F (M + N) = incM F M + incM F N := by ext; simp [incM]

theorem incM_one' {a : Type} [DecidableEq a] : incM F (1 : Matrix a a E) = 1 := by
  ext i j; by_cases h : i = j <;> simp [incM, one_apply, h]

theorem incM_zero' {a b : Type} : incM F (0 : Matrix a b E) = 0 := by ext; simp [incM]

theorem incM_transpose' {a b : Type} (M : Matrix a b E) : incM F Mᵀ = (incM F M)ᵀ := by ext; simp [incM]

theorem incM_map_cA (σ : E →ₐ[F] E) {a b : Type} (M : Matrix a b E) :
    (incM F M).map (cA σ) = incM F (M.map σ) := by ext; simp [incM, cA, inclR]

theorem conj_conj_of_cm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  apply w.embedding.injective
  have e := h.2.2.2 w.embedding
  rw [e, e, star_star]

theorem det_ne_zero_of_sig {n r s : ℕ} (B : Base F E) (J : Matrix (Fin n) (Fin n) E)
    (h : ∀ w, HasSig (J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace F))
  obtain ⟨hrs, A, hA⟩ := h w
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * J.map (B.emb w).1 * A'.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * J.map (B.emb w).1 * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  have e2 := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e2
  rw [Matrix.det_mul, Matrix.det_mul, ← e2, h0, map_zero]; simp

end Adelic

section ExtDiag
variable {A : Type} [CommRing A] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
  {ι : Matrix m k A} {Q : Matrix k m A}

theorem fromCols_add' {d : Type} (P R : Matrix d m A) (P' R' : Matrix d k A) :
    fromCols P P' + fromCols R R' = fromCols (P + R) (P' + R') := by
  ext i (j | j) <;> simp

end ExtDiag

end GlobalTheory.DoubledPlaneEmb
