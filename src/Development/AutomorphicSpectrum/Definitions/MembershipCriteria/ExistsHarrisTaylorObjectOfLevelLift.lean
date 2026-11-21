import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Complex
open scoped Classical

namespace GlobalTheory.CompanionTheory.OM

abbrev Af : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

abbrev W (κ R : Type) : Type := (κ → R) × (κ → R)

instance invTwoAf : Invertible (2 : Af) := (Invertible.map (algebraMap ℚ Af) (2 : ℚ)).copy 2 (map_ofNat _ 2).symm

variable {κ : Type} [Fintype κ]

def EF {R : Type} [CommRing R] (w w' : W κ R) : R := w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2

def ofQ (κ R : Type) [CommRing R] [Algebra ℚ R] : W κ ℚ →+ W κ R where
  toFun w := (fun i => algebraMap ℚ R (w.1 i), fun i => algebraMap ℚ R (w.2 i))
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

structure IsCx (J : W κ ℝ →L[ℝ] W κ ℝ) : Prop where
  sq : ∀ u, J (J u) = -u
  keeps : ∀ u v, EF (J u) (J v) = EF u v
  pos : ∀ u, u ≠ 0 → 0 < EF (J u) u

def drho (w : W κ ℝ) (f : (κ → ℝ) → ℂ) : (κ → ℝ) → ℂ :=
  fun x => 2 * Real.pi * I * ((x ⬝ᵥ w.2 : ℝ) : ℂ) * f x + fderiv ℝ f x w.1

def ann (J : W κ ℝ →L[ℝ] W κ ℝ) (w : W κ ℝ) (f : (κ → ℝ) → ℂ) : (κ → ℝ) → ℂ :=
  (-1 / 2 : ℂ) • (drho w f + I • drho (J w) f)

structure IsVac (J : W κ ℝ →L[ℝ] W κ ℝ) (v : (κ → ℝ) → ℂ) : Prop where
  sch : v ∈ GlobalTheory.WeilM.schFun (κ → ℝ)
  killed : ∀ w, ann J w v = 0
  unit : ∫ x, ‖v x‖ ^ 2 = 1

def hat (Γ : AddSubgroup (W κ ℚ)) : AddSubgroup (W κ Af) := (Γ.map (ofQ κ Af)).topologicalClosure

def re (Γ : AddSubgroup (W κ ℚ)) : AddSubgroup (W κ ℝ) := Γ.map (ofQ κ ℝ)

end GlobalTheory.CompanionTheory.OM

end
