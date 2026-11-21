import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

section Abstract

variable {k : Type} [Field k] {M M' M₁ M₂ M₃ : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]

structure Cx (k M : Type) [Field k] [AddCommGroup M] [Module k M] where

  C : ℤ → Submodule k M

  D : M →ₗ[k] M

namespace Cx

def IsCx (K : Cx k M) : Prop := ∀ n, ∀ a ∈ K.C n, K.D a ∈ K.C (n + 1) ∧ K.D (K.D a) = 0

def Z (K : Cx k M) (n : ℤ) : Submodule k M := K.C n ⊓ LinearMap.ker K.D

def B (K : Cx k M) (n : ℤ) : Submodule k M := (K.C (n - 1)).map K.D

abbrev H (K : Cx k M) (n : ℤ) : Type := K.Z n ⧸ (K.B n).submoduleOf (K.Z n)

end Cx

def Adj (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N : ℤ) : Prop :=
  ∀ n, ∃ ε : ℤˣ, ∀ a ∈ K.C n, ∀ b ∈ L.C (N - n - 1), β (K.D a) b = ε • β a (L.D b)

def Inj (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N n : ℤ) : Prop :=
  ∀ a ∈ K.Z n, (∀ b ∈ L.Z (N - n), β a b = 0) → a ∈ K.B n

def IsMap (K : Cx k M) (L : Cx k M') (f : M →ₗ[k] M') : Prop := ∀ n, ∀ a ∈ K.C n, f a ∈ L.C n ∧ f (K.D a) = L.D (f a)

structure SES (K₁ : Cx k M₁) (K₂ : Cx k M₂) (K₃ : Cx k M₃) (f : M₁ →ₗ[k] M₂) (g : M₂ →ₗ[k] M₃) : Prop where
  cx₁ : K₁.IsCx
  cx₂ : K₂.IsCx
  cx₃ : K₃.IsCx
  mapf : IsMap K₁ K₂ f
  mapg : IsMap K₂ K₃ g
  inj : ∀ n, ∀ a ∈ K₁.C n, f a = 0 → a = 0
  exact : ∀ n, ∀ a ∈ K₂.C n, g a = 0 ↔ ∃ a' ∈ K₁.C n, f a' = a
  surj : ∀ n, ∀ c ∈ K₃.C n, ∃ a ∈ K₂.C n, g a = c

def pt (k : Type) [Field k] : Cx k k := ⟨fun n => if n = 0 then ⊤ else ⊥, 0⟩

end Abstract

section Cech

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]

variable (k ι E) in

def deltaL : (Finset ι → E) →ₗ[k] (Finset ι → E) where
  toFun := GlobalTheory.DI.delta
  map_add' a b := by
    funext t
    simp [GlobalTheory.DI.delta, Finset.sum_add_distrib]
  map_smul' r a := by
    funext t
    simp only [GlobalTheory.DI.delta, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

def cechC (F : Finset ι → Submodule k E) (n : ℤ) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s => if s.Nonempty ∧ (s.card : ℤ) = n + 1 then F s else ⊥

def cech (F : Finset ι → Submodule k E) : Cx k (Finset ι → E) := ⟨cechC F, deltaL k ι E⟩

def totD (d : E →ₗ[k] E) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  deltaL k ι E + LinearMap.pi fun s => ((-1 : ℤ) ^ s.card) • (d ∘ₗ LinearMap.proj s)

def totC (T : ℕ → Finset ι → Submodule k E) (a b : ℕ) (n : ℤ) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s =>
    if s.Nonempty ∧ (a : ℤ) ≤ n + 1 - s.card ∧ n + 1 - s.card < b then T (n + 1 - s.card).toNat s else ⊥

def cupPair [Fintype ι] {E' : Type} [AddCommGroup E'] [Module k E'] (β : E →ₗ[k] E' →ₗ[k] k) :
    (Finset ι → E) →ₗ[k] (Finset ι → E') →ₗ[k] k :=
  ∑ j : ι, β.compl₁₂ (LinearMap.proj (Finset.univ.filter (· ≤ j))) (LinearMap.proj (Finset.univ.filter (j ≤ ·)))

end Cech

section Alg

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [Ring E] [Algebra k E]

def const (x : E) : Finset ι → E := fun s => if s.card = 1 then x else 0

end Alg

end GlobalTheory.PD
