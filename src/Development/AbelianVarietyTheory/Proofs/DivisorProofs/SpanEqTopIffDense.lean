import Mathlib

namespace GlobalTheory.Morita

structure MatrixUnits (R : Type*) [CommRing R] (N : Type*) [AddCommGroup N] [Module R N]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where

  E : ι → ι → Module.End R N
  mul_eq : ∀ i j k l, E i j * E k l = if j = k then E i l else 0
  sum_diag : ∑ i, E i i = 1

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace MatrixUnits

variable (U : MatrixUnits R N ι)

theorem apply_apply (i j k l : ι) (x : N) : U.E i j (U.E k l x) = if j = k then U.E i l x else 0 := by
  have h := LinearMap.congr_fun (U.mul_eq i j k l) x
  rw [Module.End.mul_apply] at h
  rw [h]; split_ifs <;> simp

theorem sum_apply (x : N) : ∑ i, U.E i i x = x := by
  have h := LinearMap.congr_fun U.sum_diag x
  simpa [LinearMap.sum_apply] using h

def corner (a : ι) : Submodule R N := LinearMap.range (U.E a a)

theorem mem_corner_iff (a : ι) (x : N) : x ∈ U.corner a ↔ U.E a a x = x := by
  constructor
  · rintro ⟨y, rfl⟩; rw [U.apply_apply]; simp
  · intro h; exact ⟨x, h⟩

theorem apply_mem_corner (a i : ι) (x : N) : U.E a i x ∈ U.corner a := ⟨U.E a i x, by rw [U.apply_apply]; simp⟩

def toPi (a : ι) : N ≃ₗ[R] (ι → U.corner a) where
  toFun x i := ⟨U.E a i x, U.apply_mem_corner a i x⟩
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp
  invFun v := ∑ i, U.E i a (v i)
  left_inv x := by
    simp only
    conv_rhs => rw [← U.sum_apply x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [U.apply_apply]; simp
  right_inv v := by
    ext j
    simp only [map_sum, U.apply_apply]
    simp [(U.mem_corner_iff a _).1 (v j).2]

theorem toPi_apply (a : ι) (x : N) (i : ι) : ((U.toPi a x) i : N) = U.E a i x := rfl

theorem toPi_symm_apply (a : ι) (v : ι → U.corner a) : (U.toPi a).symm v = ∑ i, U.E i a (v i) := rfl

theorem toPi_E (a i j : ι) (x : N) : U.toPi a (U.E i j x) = Pi.single i (U.toPi a x j) := by
  ext k
  rw [toPi_apply, U.apply_apply]
  by_cases h : k = i
  · subst h; simp [toPi_apply]
  · simp [h, Pi.single_apply]

end MatrixUnits

end GlobalTheory.Morita

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def ofModule [Module (Matrix ι ι R) N] [IsScalarTower R (Matrix ι ι R) N] : MatrixUnits R N ι where
  E i j := Algebra.lsmul R R N (Matrix.single i j (1 : R))
  mul_eq i j k l := by
    rw [← map_mul]
    by_cases h : j = k
    · subst h; rw [Matrix.single_mul_single_same]; simp
    · rw [Matrix.single_mul_single_of_ne (h := h)]; simp [h]
  sum_diag := by
    rw [← map_sum, Matrix.sum_single_one, map_one]

end GlobalTheory.Morita

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

def IsStable (L : Submodule R N) : Prop := ∀ i j, ∀ x ∈ L, U.E i j x ∈ L

def spread (a : ι) (L₀ : Submodule R (U.corner a)) : Submodule R N :=
  (Submodule.pi Set.univ fun _ => L₀).comap (U.toPi a).toLinearMap

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

theorem mem_of_forall {L : Submodule R N} (hL : U.IsStable L) (a : ι) {x : N} (h : ∀ i, U.E a i x ∈ L) : x ∈ L := by
  rw [← (U.toPi a).symm_apply_apply x, toPi_symm_apply]
  exact L.sum_mem fun i _ => hL i a _ (h i)

section semilinear

variable {σ : R →+* R} (F : N →ₛₗ[σ] N)

def cornerMap (a : ι) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) : U.corner a →ₛₗ[σ] U.corner a :=
  (F.domRestrict (U.corner a)).codRestrict (U.corner a) fun y => by
    rw [U.mem_corner_iff]
    simp only [LinearMap.domRestrict_apply]
    rw [← hF, (U.mem_corner_iff a _).1 y.2]

theorem cornerMap_apply (a : ι) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) (y : U.corner a) :
    (U.cornerMap F a hF y : N) = F y := rfl

end semilinear

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita
end GlobalTheory.Morita

namespace GlobalTheory.Morita
end GlobalTheory.Morita

universe w

namespace GlobalTheory.Morita

end GlobalTheory.Morita
