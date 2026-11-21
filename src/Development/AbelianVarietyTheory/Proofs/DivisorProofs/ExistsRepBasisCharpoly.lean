import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.RepModule

def Rep {R Λ n : Type} [CommRing R] [Ring Λ] [Algebra R Λ] [Fintype n] [DecidableEq n]
    (_ρ : Λ →ₐ[R] Matrix n n R) : Type := n → R

variable {R Λ n : Type} [CommRing R] [Ring Λ] [Algebra R Λ] [Fintype n] [DecidableEq n]
  (ρ : Λ →ₐ[R] Matrix n n R)

instance : AddCommGroup (Rep ρ) := inferInstanceAs (AddCommGroup (n → R))
instance : Module R (Rep ρ) := inferInstanceAs (Module R (n → R))
instance : Module.Free R (Rep ρ) := inferInstanceAs (Module.Free R (n → R))
instance : Module.Finite R (Rep ρ) := inferInstanceAs (Module.Finite R (n → R))

instance : Module Λ (Rep ρ) where
  smul a v := (ρ a *ᵥ (v : n → R) : n → R)
  one_smul v := by
    change ρ 1 *ᵥ _ = _
    rw [map_one]; exact one_mulVec _
  mul_smul a b v := by
    change ρ (a * b) *ᵥ _ = ρ a *ᵥ (ρ b *ᵥ _)
    rw [map_mul]; symm; apply mulVec_mulVec
  smul_zero a := by change ρ a *ᵥ _ = _; apply mulVec_zero
  smul_add a v w := by change ρ a *ᵥ _ = ρ a *ᵥ _ + ρ a *ᵥ _; apply mulVec_add
  add_smul a b v := by
    change ρ (a + b) *ᵥ _ = ρ a *ᵥ _ + ρ b *ᵥ _
    rw [map_add]; apply add_mulVec
  zero_smul v := by
    change ρ 0 *ᵥ _ = _
    rw [map_zero]; apply zero_mulVec

theorem smul_def (a : Λ) (v : Rep ρ) : a • v = (ρ a *ᵥ (v : n → R) : n → R) := rfl

instance : IsScalarTower R Λ (Rep ρ) where
  smul_assoc c a v := by
    change ρ (c • a) *ᵥ _ = c • (ρ a *ᵥ _)
    rw [map_smul]; apply smul_mulVec

end GlobalTheory.RepModule

