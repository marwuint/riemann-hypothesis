import Mathlib
import Formalism.ThetaSupremumBounds.StatementE

open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms

open Formalism.DimensionVariation (mono mfact nsq liftBlock)

section Calculus

variable {E κ W : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype κ]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

def dirDeriv (v : E) (F : E → ℂ) : E → ℂ := fun z => fderiv ℂ F z v

def monoDeriv (v : κ → E) (e : κ → ℕ) (F : E → ℂ) : E → ℂ :=
  (univ : Finset κ).toList.foldr (fun x G => (dirDeriv (v x))^[e x] G) F

open Classical in

def coordVec (x : κ) : κ → ℂ := Pi.single x 1

def taylorCoeff (F : (κ → ℂ) → ℂ) (e : κ → ℕ) : ℂ :=
  monoDeriv coordVec e F 0 / (mfact e : ℂ)

end Calculus

end GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms
