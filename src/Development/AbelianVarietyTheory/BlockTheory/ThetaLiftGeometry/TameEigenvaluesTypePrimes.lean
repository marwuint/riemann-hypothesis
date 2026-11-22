import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TameEigenvaluesTypePrimes

open Polynomial Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable (D : D7)

def FrobConj (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k)
    (φ : G D.host.E D.nd.Om) : Prop :=
  D.ntypes.rbar σ (D.nd.w i) (φ * D.ntypes.tg k v * φ⁻¹) =
    D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) ^ D.host.g k

end GlobalTheory.IndefiniteRowSideFullHecke.TameEigenvaluesTypePrimes

end
