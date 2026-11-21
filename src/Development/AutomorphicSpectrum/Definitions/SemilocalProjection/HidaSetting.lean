import Mathlib

noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.Loop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]

abbrev Form (E : Type) [Field E] [NumberField E] [IsCMField E] (V : Type) [AddCommGroup V]
    [Module E V] : Type := V →ₗ[E] V →ₛₗ[starRingEnd E] E

def NondegOn (h : Form E V) (A : Submodule E V) : Prop :=
  ∀ x ∈ A, (∀ y ∈ A, h x y = 0) → x = 0

def perp (h : Form E V) (A : Submodule E V) : Submodule E V where
  carrier := {x | ∀ a ∈ A, h x a = 0}
  add_mem' := fun hx hy a ha => by simp [hx a ha, hy a ha]
  zero_mem' := fun a _ => by simp
  smul_mem' := fun c x hx a ha => by simp [hx a ha]

variable [IsScalarTower (𝓞 E) E V]

def cut (Λ : Submodule (𝓞 E) V) (A : Submodule E V) : Submodule (𝓞 E) V :=
  Λ ⊓ A.restrictScalars (𝓞 E)

def mulN (g : ℕ) (Λ : Submodule (𝓞 E) V) : Submodule (𝓞 E) V :=
  Λ.map ((g : 𝓞 E) • LinearMap.id)

structure Flag (h : Form E V) (Λ : Submodule (𝓞 E) V) (r T : ℕ) where
  e : Fin r → V
  z : V
  indep : LinearIndependent E e
  iso : ∀ a b, h (e a) (e b) = 0
  orth : ∀ a, h z (e a) = 0
  mem : z ∈ Λ
  norm : h z z = -(T : E)

namespace Flag

variable {h : Form E V} {Λ : Submodule (𝓞 E) V} {r T T' : ℕ}

def X (F : Flag h Λ r T) : Submodule E V := Submodule.span E (Set.range F.e)

def Xp (F : Flag h Λ r T) : Submodule E V := F.X ⊔ Submodule.span E {F.z}

def U (F : Flag h Λ r T) : Submodule (𝓞 E) V := cut Λ F.X ⊔ Submodule.span (𝓞 E) {F.z}

def f (F : Flag h Λ r T) : Fin (r + 1) → V := Fin.snoc (α := fun _ => V) F.e F.z

def cong (F : Flag h Λ r T) (g : ℕ) : Submodule (𝓞 E) V := cut Λ F.X ⊔ mulN g Λ

def Zhat (F : Flag h Λ r T) (F' : Flag h Λ r T') : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => h (F'.f b) (F.f a)

def Dtop (F : Flag h Λ r T) (F' : Flag h Λ r T') : E := (F.Zhat F').det

def Dr (F : Flag h Λ r T) (F' : Flag h Λ r T') : E :=
  ((F.Zhat F').submatrix Fin.castSucc Fin.castSucc).det

def G (F : Flag h Λ r T) (F' : Flag h Λ r T') : E :=
  F.Dtop F' * star (F.Dtop F') - (T : E) * T' * (F.Dr F' * star (F.Dr F'))

def admitted (F : Flag h Λ r T) (F' : Flag h Λ r T') (g : ℕ) : Prop :=
  F'.cong g = F.cong g ∧ F'.z - F.z ∈ F.cong g

def UE (F : Flag h Λ r T) (F' : Flag h Λ r T') : Submodule E V := F.Xp ⊔ F'.Xp

def Transv (F : Flag h Λ r T) (F' : Flag h Λ r T') : Prop :=
  Module.finrank E (F.UE F') = 2 * r + 2 ∧ NondegOn h (F.UE F')

def IsTerm (F : Flag h Λ r T) (F' : Flag h Λ r T') (g : ℕ) : Prop := F.admitted F' g ∧ F.Transv F'

def H (F : Flag h Λ r T) (F' : Flag h Λ r T') : Submodule E V := perp h (F.UE F')

def La (F : Flag h Λ r T) (F' : Flag h Λ r T') (g : ℕ) : Submodule (𝓞 E) V where
  carrier := {x | x ∈ F.H F' ∧ ∃ a ∈ F.X, ∃ a' ∈ F'.X, x + a ∈ Λ ∧ x + a' ∈ Λ ∧ a' - a ∈ F.cong g}
  add_mem' := by
    rintro x y ⟨hx, a, ha, a', ha', h1, h2, h3⟩ ⟨hy, b, hb, b', hb', k1, k2, k3⟩
    refine ⟨add_mem hx hy, a + b, add_mem ha hb, a' + b', add_mem ha' hb', ?_, ?_, ?_⟩
    · have := add_mem h1 k1
      rwa [add_add_add_comm] at this
    · have := add_mem h2 k2
      rwa [add_add_add_comm] at this
    · have := add_mem h3 k3
      rwa [← add_sub_add_comm] at this
  zero_mem' := ⟨zero_mem _, 0, zero_mem _, 0, zero_mem _, by simp, by simp, by simp⟩
  smul_mem' := by
    rintro c x ⟨hx, a, ha, a', ha', h1, h2, h3⟩
    refine ⟨Submodule.smul_of_tower_mem _ c hx, c • a, Submodule.smul_of_tower_mem _ c ha, c • a',
      Submodule.smul_of_tower_mem _ c ha', ?_, ?_, ?_⟩
    · rw [← smul_add]; exact Λ.smul_mem c h1
    · rw [← smul_add]; exact Λ.smul_mem c h2
    · rw [← smul_sub]; exact Submodule.smul_mem _ c h3

end Flag

structure Pair {h : Form E V} {Λ : Submodule (𝓞 E) V} {r T T' : ℕ} (g : ℕ) (F : Flag h Λ r T)
    (F' F'' : Flag h Λ r T') where
  β : V →ₗ[E] V
  term' : F.IsTerm F' g
  term'' : F.IsTerm F'' g
  mapX : F'.X.map β = F''.X
  mapPerp : (perp h F'.X).map β = perp h F''.X
  isom : ∀ x ∈ perp h F'.X, ∀ y ∈ perp h F'.X, h (β x) (β y) = h x y
  mapL : ∀ x ∈ perp h F'.X, (∃ a ∈ F'.X, x + a ∈ Λ) ↔ ∃ a ∈ F''.X, β x + a ∈ Λ
  mapz : β F'.z - F''.z ∈ F''.X
  compat : ∀ l ∈ Λ, l ∈ perp h F'.X → ∀ a ∈ F''.X, β l + a ∈ Λ → β l + a - l ∈ F.cong g

namespace Pair

variable {h : Form E V} {Λ : Submodule (𝓞 E) V} {r T T' g : ℕ} {F : Flag h Λ r T}
  {F' F'' : Flag h Λ r T'}

def Th (P : Pair g F F' F'') : Submodule E V :=
  F.H F' ⊓ (((F.H F'').comap (LinearMap.snd E V V) ⊓
    F.X.comap (LinearMap.fst E V V - LinearMap.snd E V V) ⊓
    F''.X.comap (P.β ∘ₗ LinearMap.fst E V V - LinearMap.snd E V V)).map (LinearMap.fst E V V))

def M (P : Pair g F F' F'') : Submodule (𝓞 E) V := cut (F.La F' g) P.Th

def b (P : Pair g F F' F'') (x y : V) : E := h x y - h (P.β x) y

def s0 (P : Pair g F F' F'') (k : ℕ) : ℕ := k - Module.finrank E P.Th

end Pair

end GlobalTheory.CompanionTheory.Loop
