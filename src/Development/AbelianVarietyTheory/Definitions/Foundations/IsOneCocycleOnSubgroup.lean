import Mathlib

noncomputable section

namespace GlobalTheory.KCoh

variable {R : Type*} [CommRing R] {G : Type*} [Group G]
variable {M M' M'' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

def tw (χ : G →* Rˣ) (ρ : Representation R G M) : Representation R G M where
  toFun g := (χ g : R) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext m
    simp [mul_smul, smul_comm (χ h : R) (χ g : R)]

def sh (S : Type*) [MulAction G S] (ρ : Representation R G M) : Representation R G (S → M) where
  toFun g :=
    { toFun := fun f s => ρ g (f (g⁻¹ • s))
      map_add' := fun f f' => by funext s; simp
      map_smul' := fun c f => by funext s; simp }
  map_one' := by ext f s; simp
  map_mul' g h := by ext f s; simp [mul_smul]

def pull {S S' : Type*} (π : S' → S) : (S → M) →ₗ[R] (S' → M) := LinearMap.funLeft R M π

def ptw (S : Type*) (β : M →ₗ[R] M' →ₗ[R] M'') : (S → M) →ₗ[R] (S → M') →ₗ[R] (S → M'') :=
  LinearMap.mk₂ R (fun f f' s => β (f s) (f' s))
    (fun _ _ _ => by funext s; simp) (fun _ _ _ => by funext s; simp)
    (fun _ _ _ => by funext s; simp) (fun _ _ _ => by funext s; simp)

def fam {S : Type*} (f : S → M →ₗ[R] M') : (S → M) →ₗ[R] (S → M') where
  toFun m s := f s (m s)
  map_add' _ _ := by funext s; simp
  map_smul' _ _ := by funext s; simp

@[simp] theorem sh_apply (S : Type*) [MulAction G S] (ρ : Representation R G M) (g : G) (f : S → M) (s : S) :
    sh S ρ g f s = ρ g (f (g⁻¹ • s)) := rfl

@[simp] theorem tw_apply (χ : G →* Rˣ) (ρ : Representation R G M) (g : G) (m : M) :
    tw χ ρ g m = (χ g : R) • ρ g m := rfl

@[simp] theorem pull_apply {S S' : Type*} (π : S' → S) (f : S → M) (s : S') : pull (R := R) π f s = f (π s) := rfl

@[simp] theorem ptw_apply (S : Type*) (β : M →ₗ[R] M' →ₗ[R] M'') (f : S → M) (f' : S → M') (s : S) :
    ptw S β f f' s = β (f s) (f' s) := rfl

@[simp] theorem fam_apply {S : Type*} (f : S → M →ₗ[R] M') (m : S → M) (s : S) : fam f m s = f s (m s) := rfl

end GlobalTheory.KCoh
