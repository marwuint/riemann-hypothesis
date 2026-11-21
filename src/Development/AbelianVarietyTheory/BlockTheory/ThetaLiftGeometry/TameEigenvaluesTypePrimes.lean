import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TameEigenvaluesTypePrimes

open Polynomial Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable (D : D7)

def TameEigenvalues (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
      Matrix (Fin D.R.r) (Fin D.R.r)
        (Fb (D.what₂.places.resChar (D.nd.w i)) (D.what₂.places.resChar_prime (D.nd.w i)))).charpoly =
    ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
      X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod

def FrobConj (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k)
    (φ : G D.host.E D.nd.Om) : Prop :=
  D.ntypes.rbar σ (D.nd.w i) (φ * D.ntypes.tg k v * φ⁻¹) =
    D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) ^ D.host.g k

end GlobalTheory.IndefiniteRowSideFullHecke.TameEigenvaluesTypePrimes

end
