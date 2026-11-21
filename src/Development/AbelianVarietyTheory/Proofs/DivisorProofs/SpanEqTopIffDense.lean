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

theorem ofModule_E [Module (Matrix ι ι R) N] [IsScalarTower R (Matrix ι ι R) N] (i j : ι) (x : N) :
    (ofModule (R := R)).E i j x = Matrix.single i j (1 : R) • x := rfl
end GlobalTheory.Morita

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

theorem toPi_corner (a : ι) (y : U.corner a) : U.toPi a y = Pi.single a y := by
  ext i
  rw [toPi_apply, ← (U.mem_corner_iff a _).1 y.2, U.apply_apply]
  by_cases h : i = a
  · subst h; simp [(U.mem_corner_iff i _).1 y.2]
  · simp [h, Pi.single_apply, Ne.symm h]

def IsStable (L : Submodule R N) : Prop := ∀ i j, ∀ x ∈ L, U.E i j x ∈ L

def cornerPart (a : ι) (L : Submodule R N) : Submodule R (U.corner a) := L.comap (U.corner a).subtype

def spread (a : ι) (L₀ : Submodule R (U.corner a)) : Submodule R N :=
  (Submodule.pi Set.univ fun _ => L₀).comap (U.toPi a).toLinearMap

theorem mem_cornerPart {a : ι} {L : Submodule R N} {y : U.corner a} : y ∈ U.cornerPart a L ↔ (y : N) ∈ L :=
  Iff.rfl

theorem mem_spread {a : ι} {L₀ : Submodule R (U.corner a)} {x : N} :
    x ∈ U.spread a L₀ ↔ ∀ i, U.toPi a x i ∈ L₀ := by
  simp [spread, Submodule.mem_pi]

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

theorem mem_of_forall {L : Submodule R N} (hL : U.IsStable L) (a : ι) {x : N} (h : ∀ i, U.E a i x ∈ L) : x ∈ L := by
  rw [← (U.toPi a).symm_apply_apply x, toPi_symm_apply]
  exact L.sum_mem fun i _ => hL i a _ (h i)

theorem spread_isStable (a : ι) (L₀ : Submodule R (U.corner a)) : U.IsStable (U.spread a L₀) := by
  intro i j x hx
  rw [mem_spread] at hx ⊢
  intro k
  rw [toPi_E]
  by_cases h : k = i
  · subst h; simpa using hx j
  · simp [Pi.single_apply, h, L₀.zero_mem]

theorem cornerPart_spread (a : ι) (L₀ : Submodule R (U.corner a)) : U.cornerPart a (U.spread a L₀) = L₀ := by
  ext y
  rw [mem_cornerPart, mem_spread, toPi_corner]
  constructor
  · intro h; simpa using h a
  · intro h i
    by_cases hi : i = a
    · subst hi; simpa using h
    · simp [Pi.single_apply, hi, L₀.zero_mem]

theorem spread_cornerPart {L : Submodule R N} (hL : U.IsStable L) (a : ι) : U.spread a (U.cornerPart a L) = L := by
  ext x
  rw [mem_spread]
  constructor
  · intro h; exact U.mem_of_forall hL a fun i => h i
  · intro h i; exact hL a i x h

def latIso (a : ι) : {L : Submodule R N // U.IsStable L} ≃o Submodule R (U.corner a) where
  toFun L := U.cornerPart a L.1
  invFun L₀ := ⟨U.spread a L₀, U.spread_isStable a L₀⟩
  left_inv L := Subtype.ext (U.spread_cornerPart L.2 a)
  right_inv L₀ := U.cornerPart_spread a L₀
  map_rel_iff' {L L'} := by
    constructor
    · intro h
      show L.1 ≤ L'.1
      rw [← U.spread_cornerPart L.2 a, ← U.spread_cornerPart L'.2 a]
      intro x hx
      rw [mem_spread] at hx ⊢
      exact fun i => h (hx i)
    · intro h y hy; exact h hy

theorem latIso_apply (a : ι) (L : {L : Submodule R N // U.IsStable L}) : U.latIso a L = U.cornerPart a L.1 := rfl

theorem latIso_symm_apply (a : ι) (L₀ : Submodule R (U.corner a)) : ((U.latIso a).symm L₀).1 = U.spread a L₀ := rfl

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
