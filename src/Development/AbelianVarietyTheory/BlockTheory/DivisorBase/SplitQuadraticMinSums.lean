import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable {H : Host E} {Dw : Datum H}

def IsBig (k : ℕ) (f : Lt1 Dw) : Prop := InPsi H f.1 ∧ k ≤ rk f + 1

def IsSpread (k : ℕ) (f : Lt1 Dw) : Prop := InPsi H f.1 ∧ rk f + 2 ≤ k

def IsSmall (f : Lt1 Dw) : Prop := ¬ InPsi H f.1

theorem not_isBig_iff (k : ℕ) (f : Lt1 Dw) : ¬ IsBig k f ↔ IsSmall f ∨ IsSpread k f := by
  unfold IsBig IsSmall IsSpread
  by_cases h : InPsi H f.1
  · simp only [h, true_and, not_true, false_or]; omega
  · simp [h]

open Classical in

def sumBig (k : ℕ) (cx : Lt1 Dw → ℕ) : ℕ := ∑ f ∈ Finset.univ.filter (IsBig k), cx f

open Classical in

def sumSmallSpread (k : ℕ) (cx : Lt1 Dw → ℕ) : ℕ :=
  ∑ f ∈ Finset.univ.filter (fun f => IsSmall f ∨ IsSpread k f), rk f * cx f

end GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification
