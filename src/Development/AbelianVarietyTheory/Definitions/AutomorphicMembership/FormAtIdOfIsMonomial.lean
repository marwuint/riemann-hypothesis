import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef.StepCheck

section Fun

variable {O : Type} [CommRing O]

theorem comb_eval (a b : ℕ) (ψ φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X → X → ℝ) :
    (comb a ψ b φ).eval X B = a * ψ.eval X B + b * φ.eval X B := rfl

variable {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

variable {bar : O → O} {φ φ' : InvFun O}

end Fun

end GlobalTheory.TorRef.StepCheck
