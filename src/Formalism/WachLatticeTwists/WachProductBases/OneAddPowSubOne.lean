import Mathlib
import Formalism.CoboundaryTransfers.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

structure HidaSetting (O A : Type) [CommRing O] [CommRing A] [Algebra O A] where
  ℓ : ℕ
  hℓ : ℓ.Prime
  s : ℕ
  hs : 1 ≤ s
  hs2 : ℓ = 2 → 2 ≤ s
  φ : A →ₐ[O] A
  γ : A →ₐ[O] A
  comm : ∀ a, φ (γ a) = γ (φ a)
  π : A
  φπ : φ π = (1 + π) ^ ℓ - 1
  c₀ : O
  c₁ : A
  γπ : γ (1 + π) = (1 + π) * (1 + (⇑φ)^[s] π * (algebraMap O A c₀ + (⇑φ)^[s] π * c₁))

namespace HidaSetting

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A)

def X : A := (⇑S.φ)^[S.s - 1] S.π

def Q : A := ∑ k ∈ Finset.range S.ℓ, ((S.ℓ.choose (k + 1) : ℕ) : A) * S.X ^ k

def ε : A := 1 + S.π

def u : O := 1 + (S.ℓ : O) ^ S.s * S.c₀

theorem φ_ε : S.φ S.ε = S.ε ^ S.ℓ := by
  simp [ε, S.φπ]

theorem iter_π (k : ℕ) : (⇑S.φ)^[k] S.π = S.ε ^ (S.ℓ ^ k) - 1 := by
  induction k with
  | zero => simp [ε]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_sub, map_pow, map_one, S.φ_ε, ← pow_mul, pow_succ']

theorem X_eq : S.X = S.ε ^ (S.ℓ ^ (S.s - 1)) - 1 := S.iter_π _

theorem one_add_pow_sub_one (x : A) (n : ℕ) :
    (1 + x) ^ n - 1 = x * ∑ k ∈ Finset.range n, ((n.choose (k + 1) : ℕ) : A) * x ^ k := by
  rw [add_comm, add_pow, Finset.sum_range_succ', Finset.mul_sum]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem φ_X : S.φ S.X = S.X * S.Q := by
  have h : S.φ S.X = (1 + S.X) ^ S.ℓ - 1 := by
    rw [S.X_eq, map_sub, map_pow, map_one, S.φ_ε]
    ring
  rw [h, Q, one_add_pow_sub_one]

def base : Formalism.CoboundaryTransfers.Base O A where
  p := S.ℓ
  hp := S.hℓ
  φ := S.φ
  γ := S.γ
  X := S.X
  Q := S.Q
  comm := S.comm
  φX := ⟨S.Q, S.φ_X⟩

end HidaSetting

end Formalism.RepresentationBoundsCohomology.N1
