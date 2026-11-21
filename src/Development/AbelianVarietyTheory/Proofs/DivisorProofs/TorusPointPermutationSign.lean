import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRenumber

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def permCLE (σ : Equiv.Perm (Fin g)) : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ σ).toContinuousLinearEquiv

@[simp] theorem permCLE_apply (σ : Equiv.Perm (Fin g)) (w : Fin g → ℂ) : permCLE σ w = w ∘ σ := rfl

end GlobalTheory.TorusRenumber

namespace GlobalTheory.TorusRenumber

end GlobalTheory.TorusRenumber

namespace GlobalTheory.TorusRenumber

end GlobalTheory.TorusRenumber
