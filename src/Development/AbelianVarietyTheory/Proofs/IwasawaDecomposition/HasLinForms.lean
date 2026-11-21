import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef

section Vals

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem InvFun.evalZ_comb [Module.Finite O X] (a : ℕ) (ψ : InvFun O) (b : ℕ) (φ : InvFun O)
    (β : LinearMap.BilinForm ℤ X) : (comb a ψ b φ).evalZ β = a * ψ.evalZ β + b * φ.evalZ β := rfl

end Vals

end GlobalTheory.TorRef

namespace GlobalTheory.TorRef

end GlobalTheory.TorRef
