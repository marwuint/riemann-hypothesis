import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et Polynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.CurveCut

section Defs
variable (k : Type) [Field k]

abbrev Kb : Type := AlgebraicClosure (RatFunc k)

abbrev Gal : Type := Kb k ≃ₐ[RatFunc k] Kb k

abbrev OK : Type := integralClosure k[X] (Kb k)

def geo : Subgroup (Gal k) where
  carrier := {g | ∀ x : Kb k, IsAlgebraic k x → g x = x}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x hx := by rw [AlgEquiv.mul_apply, hb x hx, ha x hx]
  inv_mem' {a} ha x hx := a.symm_apply_eq.2 (ha x hx).symm

instance geo_normal : (geo k).Normal := ⟨fun g hg σ x hx => by
  have h : IsAlgebraic k (σ.symm x) := hx.algHom (σ.symm.toAlgHom.restrictScalars k)
  change σ (g (σ.symm x)) = x
  rw [hg _ h, σ.apply_symm_apply]⟩

variable {k}

def Inert (h : k[X]) (g : Gal k) : Prop := ∃ P : Ideal (OK k), P.IsPrime ∧ algebraMap k[X] (OK k) h ∉ P ∧
  ∀ s s' : OK k, (s' : Kb k) = g s → s' - s ∈ P

def ram (h : k[X]) : Subgroup (Gal k) := Subgroup.normalClosure {g | Inert h g}

instance ram_normal (h : k[X]) : (ram h).Normal := Subgroup.normalClosure_normal

variable (l : ℕ) [Fact l.Prime] {V : Type 1} [AddCommGroup V] [Module ℚ_[l] V]

variable {l}

end Defs

end LateralTheory.EWeil.CurveCut

end
