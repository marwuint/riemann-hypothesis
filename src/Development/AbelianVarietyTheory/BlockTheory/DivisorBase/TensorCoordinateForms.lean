import Mathlib
import Formalism.ThetaSupremumBounds.StatementE

open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms

def dirDeriv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) (F : V → ℂ) : V → ℂ :=
  fun z => fderiv ℂ F z v

def wordDeriv {κ V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : κ → V) (w : List κ)
    (F : V → ℂ) : V → ℂ :=
  w.foldr (fun x G => dirDeriv (v x) G) F

def IsSpelling {κ : Type} [DecidableEq κ] (w : (κ → ℕ) → List κ) : Prop :=
  ∀ e x, (w e).count x = e x

def coordVec {κ : Type} [DecidableEq κ] (p : κ) : κ → ℂ := Pi.single p 1

end GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms
