import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LogPeriodsModel

open Matrix Metric GroundTheory.Heights₂.Heights.Regular

def stdE : LinearMap.BilinForm ℤ (Fin 2 → ℤ) :=
  LinearMap.mk₂ ℤ (fun x y => x 1 * y 0 - x 0 * y 1)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

theorem stdE_apply (x y : Fin 2 → ℤ) : stdE x y = x 1 * y 0 - x 0 * y 1 := rfl

def per (w : Fin 1 → ℂ) : (Fin 2 → ℤ) →+ (Fin 1 → ℂ) where
  toFun x := fun _ => (x 0 : ℂ) + (x 1 : ℂ) * (w 0 / (2 * Real.pi * Complex.I))
  map_zero' := by funext; simp
  map_add' x y := by funext; simp; ring

theorem per_apply (w : Fin 1 → ℂ) (x : Fin 2 → ℤ) (j : Fin 1) :
    per w x j = (x 0 : ℂ) + (x 1 : ℂ) * (w 0 / (2 * Real.pi * Complex.I)) := rfl

theorem P_injective {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : LogPeriods n a g Λ)
    {w : Fin n → ℂ} (hw : w ∈ logCover L.a_le) : Function.Injective (L.P w) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply L.unimod.1
  refine LinearMap.ext fun y => ?_
  have := L.im w hw x y
  rw [hx] at this
  simp only [zero_dotProduct, Complex.zero_im] at this
  simp only [map_zero, LinearMap.zero_apply]
  exact_mod_cast this.symm

end GlobalTheory.CompanionTheory.Ar.Flat.LogPeriodsModel
