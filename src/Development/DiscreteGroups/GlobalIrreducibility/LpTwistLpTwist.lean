import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section W

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

variable (h) in

def degDvd (n : ℕ) : Subgroup (Weil h) where
  carrier := {σ | (n : ℤ) ∣ deg σ}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show (n : ℤ) ∣ deg (a * b)
    rw [deg_mul]; exact dvd_add ha hb
  inv_mem' := fun {a} ha => by
    show (n : ℤ) ∣ deg a⁻¹
    rw [deg_inv]; exact (dvd_neg).mpr ha

end W

end DiscreteGroups.sglob.DzType

end
