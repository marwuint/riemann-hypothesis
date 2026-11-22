import Mathlib

noncomputable section

namespace UpperTheory.V.AlgebraTools

structure Cx (A : Type) [CommRing A] where
  X : ℕ → Type
  [grp : ∀ n, AddCommGroup (X n)]
  [mod : ∀ n, Module A (X n)]
  d : ∀ n, X n →ₗ[A] X (n + 1)
  dd : ∀ n x, d (n + 1) (d n x) = 0

attribute [instance] Cx.grp Cx.mod

namespace Cx

variable {A : Type} [CommRing A]

def Z (K : Cx A) (n : ℕ) : Submodule A (K.X n) := LinearMap.ker (K.d n)

def B (K : Cx A) : ∀ n : ℕ, Submodule A (K.X n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (K.d n)

abbrev H (K : Cx A) (n : ℕ) : Type := K.Z n ⧸ (K.B n).comap (K.Z n).subtype

abbrev cls (K : Cx A) {n : ℕ} (z : K.Z n) : K.H n := Submodule.Quotient.mk z

structure Hom (K L : Cx A) where
  f : ∀ n, K.X n →ₗ[A] L.X n
  comm : ∀ n x, f (n + 1) (K.d n x) = L.d n (f n x)

namespace Hom

variable {K L N : Cx A}

def id (K : Cx A) : Hom K K where
  f _ := LinearMap.id
  comm _ _ := rfl

def comp (ψ : Hom L N) (φ : Hom K L) : Hom K N where
  f n := ψ.f n ∘ₗ φ.f n
  comm n x := (congrArg (ψ.f (n + 1)) (φ.comm n x)).trans (ψ.comm n _)

def smul (a : A) (φ : Hom K L) : Hom K L where
  f n := a • φ.f n
  comm n x := by rw [LinearMap.smul_apply, LinearMap.smul_apply, φ.comm, map_smul]

def sub (φ ψ : Hom K L) : Hom K L where
  f n := φ.f n - ψ.f n
  comm n x := by rw [LinearMap.sub_apply, LinearMap.sub_apply, φ.comm, ψ.comm, map_sub]

def Z (φ : Hom K L) (n : ℕ) : K.Z n →ₗ[A] L.Z n :=
  (φ.f n).restrict fun x hx => by
    have h0 : K.d n x = 0 := hx
    exact (φ.comm n x).symm.trans (by rw [h0, map_zero])

theorem map_B (φ : Hom K L) (n : ℕ) : ∀ x ∈ K.B n, φ.f n x ∈ L.B n := by
  rcases n with _ | n
  · intro x hx
    rw [(Submodule.mem_bot A).1 hx, map_zero]
    exact zero_mem _
  · rintro _ ⟨y, rfl⟩
    exact ⟨φ.f n y, (φ.comm n y).symm⟩

def H (φ : Hom K L) (n : ℕ) : K.H n →ₗ[A] L.H n :=
  Submodule.mapQ _ _ (φ.Z n) fun z hz => φ.map_B n z.1 hz

theorem H_cls (φ : Hom K L) {n : ℕ} (z : K.Z n) : φ.H n (K.cls z) = L.cls (φ.Z n z) := rfl

end Hom

def prod (K L : Cx A) : Cx A where
  X n := K.X n × L.X n
  d n := (K.d n).prodMap (L.d n)
  dd n x := Prod.ext (K.dd n x.1) (L.dd n x.2)

def pi {ι : Type} (K : ι → Cx A) : Cx A where
  X n := ∀ i, (K i).X n
  d n := LinearMap.pi fun i => (K i).d n ∘ₗ LinearMap.proj i
  dd n x := funext fun i => (K i).dd n (x i)

def up (L : Cx A) : ℕ → Type
  | 0 => PUnit
  | n + 1 => L.X n

instance upGrp (L : Cx A) : ∀ n, AddCommGroup (L.up n)
  | 0 => inferInstanceAs (AddCommGroup PUnit)
  | n + 1 => L.grp n

instance upMod (L : Cx A) : ∀ n, Module A (L.up n)
  | 0 => inferInstanceAs (Module A PUnit)
  | n + 1 => L.mod n

def upD (L : Cx A) : ∀ n, L.up n →ₗ[A] L.X n
  | 0 => 0
  | n + 1 => L.d n

theorem d_upD (L : Cx A) (n : ℕ) (y : L.up n) : L.d n (L.upD n y) = 0 := by
  rcases n with _ | n
  · exact map_zero _
  · exact L.dd n y

variable {K L N : Cx A}

def fib (φ : Hom K L) : Cx A where
  X n := K.X n × L.up n
  d n := (K.d n ∘ₗ LinearMap.fst A _ _).prod
    (show K.X n × L.up n →ₗ[A] L.X n from φ.f n ∘ₗ LinearMap.fst A _ _ - L.upD n ∘ₗ LinearMap.snd A _ _)
  dd n x := Prod.ext (K.dd n x.1) <| by
    change φ.f (n + 1) (K.d n x.1) - L.d n (φ.f n x.1 - L.upD n x.2) = 0
    rw [map_sub, L.d_upD, φ.comm, sub_zero, sub_self]

theorem fib_d (φ : Hom K L) (n : ℕ) (x : K.X n) (y : L.up n) :
    (fib φ).d n (x, y) = (K.d n x, show L.X n from φ.f n x - L.upD n y) := rfl

structure SES (i : Hom K L) (p : Hom L N) : Prop where
  inj : ∀ n, Function.Injective (i.f n)
  ex : ∀ n, Function.Exact (i.f n) (p.f n)
  surj : ∀ n, Function.Surjective (p.f n)

def single (M : Type) [AddCommGroup M] [Module A M] : Cx A where
  X n := match n with | 0 => M | _ + 1 => PUnit
  grp n := match n with | 0 => ‹AddCommGroup M› | _ + 1 => inferInstanceAs (AddCommGroup PUnit)
  mod n := match n with | 0 => ‹Module A M› | _ + 1 => (inferInstance : Module A PUnit)
  d _ := 0
  dd _ _ := rfl

instance instInhabited : Inhabited (Cx A) := ⟨single PUnit⟩

end Cx

section Cochains

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

variable [TopologicalSpace G] [TopologicalSpace M]

variable [IsTopologicalAddGroup M] [ContinuousConstSMul A M]

end Cochains

end UpperTheory.V.AlgebraTools

end
