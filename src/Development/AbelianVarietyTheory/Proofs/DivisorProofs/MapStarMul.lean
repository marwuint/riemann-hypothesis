import Mathlib

noncomputable section

open scoped Matrix

namespace GlobalTheory.IndLine.Iwasawa

section Exp

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open scoped Matrix in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in

theorem _root_.GlobalTheory.IndLine.Iwasawa.exp_mul_eq {A : Matrix m m ℂ} {D : Matrix n n ℂ}
    {B : Matrix m n ℂ} (h : A * B = B * D) :
    NormedSpace.exp A * B = B * NormedSpace.exp D := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have hk : ∀ k : ℕ, A ^ k * B = B * D ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have hA := NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have hD := NormedSpace.expSeries_summable' (𝕂 := ℂ) D
  let L : Matrix m m ℂ →L[ℂ] Matrix m n ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun X => X * B, map_add' := fun X Y => Matrix.add_mul X Y B,
      map_smul' := fun c X => Matrix.smul_mul c X B }
  let L' : Matrix n n ℂ →L[ℂ] Matrix m n ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun X => B * X, map_add' := fun X Y => Matrix.mul_add B X Y,
      map_smul' := fun c X => Matrix.mul_smul B c X }
  have e1 := L.map_tsum hA
  have e2 := L'.map_tsum hD
  simp only [L, L', LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk] at e1 e2
  rw [NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]
  show (∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • A ^ k)) * B = B * ∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • D ^ k)
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  funext k
  rw [Matrix.smul_mul, Matrix.mul_smul, hk]

end Exp

section Ring

variable {R : Type} [Ring R]

structure Grading (p r q θ : R) : Prop where
  pp : p * p = p
  qq : q * q = q
  pq : p * q = 0
  qp : q * p = 0
  sum : r = 1 - p - q
  θθ : θ * θ = 1
  θp : θ * p = q * θ

namespace Grading

end Grading

end Ring

section Adj

variable {m : Type} [Fintype m] [DecidableEq m]

def Adj (N A B : Matrix m m ℂ) : Prop := Aᵀ * N = N * B.map star

theorem map_star_mul' {m n p : Type} [Fintype n] (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    (A * B).map star = A.map star * B.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

variable {N A B A' B' : Matrix m m ℂ}

theorem Adj.mul (h : Adj N A B) (h' : Adj N A' B') : Adj N (A * A') (B' * B) := by
  rw [Adj, Matrix.transpose_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, h', map_star_mul',
    Matrix.mul_assoc]

theorem Adj.add (h : Adj N A B) (h' : Adj N A' B') : Adj N (A + A') (B + B') := by
  rw [Adj, Matrix.transpose_add, Matrix.add_mul, h, h', Matrix.map_add _ star_add, Matrix.mul_add]

theorem Adj.sub (h : Adj N A B) (h' : Adj N A' B') : Adj N (A - A') (B - B') := by
  rw [Adj, Matrix.transpose_sub, Matrix.sub_mul, h, h', Matrix.map_sub _ star_sub, Matrix.mul_sub]

variable {p r q θ Z : Matrix m m ℂ}

end Adj

section Plane

variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def prX (c : A →+* A) (J : Matrix m m A) (x y : m → A) : Matrix m m A := Matrix.vecMulVec x (J *ᵥ (c ∘ y))

def prY (c : A →+* A) (J : Matrix m m A) (x y : m → A) : Matrix m m A := -Matrix.vecMulVec y (J *ᵥ (c ∘ x))

structure Hyp (c : A →+* A) (J : Matrix m m A) (x y : m → A) (ι : Matrix m n A) (ι' : Matrix n m A) : Prop where
  cc : ∀ a, c (c a) = a
  skew : J.map c = -Jᵀ
  xx : x ⬝ᵥ J *ᵥ (c ∘ x) = 0
  yy : y ⬝ᵥ J *ᵥ (c ∘ y) = 0
  xy : x ⬝ᵥ J *ᵥ (c ∘ y) = 1
  yx : y ⬝ᵥ J *ᵥ (c ∘ x) = -1
  ιx : (J *ᵥ (c ∘ x)) ᵥ* ι = 0
  ιy : (J *ᵥ (c ∘ y)) ᵥ* ι = 0
  left : ι' * ι = 1
  right : ι * ι' = 1 - prX c J x y - prY c J x y

variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}

theorem map_mulVec' (f : A →+* A') (hf : ∀ a, f (c a) = c' (f a)) (J : Matrix m m A) (x : m → A) :
    f ∘ (J *ᵥ (c ∘ x)) = J.map f *ᵥ (c' ∘ (f ∘ x)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, hf]

theorem prX_map (f : A →+* A') (hf : ∀ a, f (c a) = c' (f a)) :
    (prX c J x y).map f = prX c' (J.map f) (f ∘ x) (f ∘ y) := by
  ext i j
  simp [prX, Matrix.vecMulVec_apply, ← map_mulVec' f hf]

theorem prY_map (f : A →+* A') (hf : ∀ a, f (c a) = c' (f a)) :
    (prY c J x y).map f = prY c' (J.map f) (f ∘ x) (f ∘ y) := by
  ext i j
  simp [prY, Matrix.vecMulVec_apply, ← map_mulVec' f hf]

theorem Hyp.map (h : Hyp c J x y ι ι') (f : A →+* A') (hf : ∀ a, f (c a) = c' (f a)) (hc : ∀ a, c' (c' a) = a) :
    Hyp c' (J.map f) (f ∘ x) (f ∘ y) (ι.map f) (ι'.map f) := by
  have d : ∀ u v : m → A, (f ∘ u) ⬝ᵥ J.map f *ᵥ (c' ∘ (f ∘ v)) = f (u ⬝ᵥ J *ᵥ (c ∘ v)) := fun u v => by
    rw [← map_mulVec' f hf, RingHom.map_dotProduct]
  have e : ∀ v : m → A, (J *ᵥ (c ∘ v)) ᵥ* ι = 0 → (J.map f *ᵥ (c' ∘ (f ∘ v))) ᵥ* ι.map f = 0 := fun v hv => by
    funext j
    rw [← map_mulVec' f hf, ← RingHom.map_vecMul, hv, Pi.zero_apply, map_zero, Pi.zero_apply]
  refine ⟨hc, ?_, by rw [d, h.xx, map_zero], by rw [d, h.yy, map_zero], by rw [d, h.xy, map_one],
    by rw [d, h.yx, map_neg, map_one], e x h.ιx, e y h.ιy, ?_, ?_⟩
  · ext i j
    have := congrArg f (congrFun (congrFun h.skew i) j)
    simpa [hf] using this
  · rw [← Matrix.map_mul, h.left, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, h.right, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _),
      Matrix.map_one _ (map_zero _) (map_one _), prX_map f hf, prY_map f hf]

namespace Hyp

end Hyp

end Plane

end GlobalTheory.IndLine.Iwasawa

end
