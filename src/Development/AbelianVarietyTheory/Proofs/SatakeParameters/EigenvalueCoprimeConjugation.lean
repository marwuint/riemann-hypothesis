import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TameEigenvaluesTypePrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition

noncomputable section

namespace GlobalTheory.Proof.EigenvalueCoprimeConjugation

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual Formalism.CyclotomicNorms ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.WeilDeligne GlobalTheory.IndefiniteRowSideFullHecke.TameEigenvaluesTypePrimes

variable (D : D7)

def EigenClause (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
      Matrix (Fin D.R.r) (Fin D.R.r) _) =
    ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
      X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod

theorem first_iff : GlobalTheory.RowCopy.JointOccurrenceCondition D ↔
    ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k), D.ntypes.cuspidal σ →
      TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
      ∀ i : D.nd.Loc, D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
        EigenClause D σ i k v ∧ ∃ φ : G D.host.E D.nd.Om, FrobConj D σ i k v φ := Iff.rfl

theorem normV_plGw (k : Fin 2) (v : D.nd.PlG k) : normV (D.naut.plGw k v) = D.host.g k :=
  normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v)

end GlobalTheory.Proof.EigenvalueCoprimeConjugation

end
