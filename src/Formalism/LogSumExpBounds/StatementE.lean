import Mathlib

namespace Formalism.NuclearRankWeightBounds.E

section
variable {K : Type*} [CommRing K] [StarRing K] {V : Type*} [AddCommGroup V] [Module K V]

def IsHerm (h : V →ₗ[K] V →ₗ⋆[K] K) : Prop := ∀ v w, h w v = star (h v w)

def tau (h : V →ₗ[K] V →ₗ⋆[K] K) (x u : V) (v : V) : V :=
  v + h v x • u - h v u • x
end

def mass {C : Type*} [Fintype C] (wt : C → C → ℝ) (c : C) : ℝ := ∑ c', wt c c'

end Formalism.NuclearRankWeightBounds.E
