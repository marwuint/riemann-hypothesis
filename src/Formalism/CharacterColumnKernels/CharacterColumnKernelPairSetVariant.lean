import Formalism.CharacterColumnKernels.StatementN

open Finset Classical

noncomputable section

namespace Formalism.NG

section Cochains
variable {O : Type*} [CommRing O] {D : Type*} [Group D] {M : Type*} [AddCommGroup M] [Module O M]

def coD0 (ρ : Representation O D M) : M →ₗ[O] (D → M) where
  toFun v g := ρ g v - v
  map_add' v w := by ext g; simp only [map_add, Pi.add_apply]; abel
  map_smul' c v := by ext g; simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]

def coB1 (ρ : Representation O D M) : Submodule O (D → M) := LinearMap.range (coD0 ρ)

def characterColumnKernelSet (ρ : Representation O D M) : Set (D → M) :=
  {c | ∀ g h, c (g * h) = c g + ρ g (c h)}

def characterColumnKernelPairSetVariant (ρ : Representation O D M) : Set (D → D → M) :=
  {c | ∀ g h k, ρ g (c h k) - c (g * h) k + c g (h * k) - c g h = 0}

end Cochains

def cup1 {O D M₁ M₂ N : Type*} [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁]
    [AddCommGroup M₂] [Module O M₂] [AddCommGroup N] [Module O N]
    (ρ₂ : Representation O D M₂) (β : M₁ →ₗ[O] M₂ →ₗ[O] N) (a : D → M₁) (b : D → M₂) :
    D → D → N :=
  fun g h => β (a g) (ρ₂ g (b h))

def IsEquivPairing {O D M₁ M₂ N : Type*} [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁]
    [AddCommGroup M₂] [Module O M₂] [AddCommGroup N] [Module O N]
    (ρ₁ : Representation O D M₁) (ρ₂ : Representation O D M₂) (ρN : Representation O D N)
    (β : M₁ →ₗ[O] M₂ →ₗ[O] N) : Prop :=
  ∀ g m n, β (ρ₁ g m) (ρ₂ g n) = ρN g (β m n)

def IsEquivMap {O D M M' : Type*} [CommRing O] [Group D] [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (ρ : Representation O D M) (ρ' : Representation O D M')
    (f : M →ₗ[O] M') : Prop :=
  ∀ g m, f (ρ g m) = ρ' g (f m)

def colD {A T' K V G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [SMulCommClass A K V]
    (r : G →* A) (χ : G →* T'ˣ) (D : Subgroup G) : V →ₗ[K] (D → V) where
  toFun v g := ((((χ g)⁻¹ : T'ˣ) : T') • r g) • v - v
  map_add' v w := by ext g; simp only [smul_add, Pi.add_apply]; abel
  map_smul' c v := by ext g; simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, smul_comm]

end Formalism.NG
