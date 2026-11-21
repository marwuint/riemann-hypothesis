import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

def UnitChartAt (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (x : X) :
    Prop :=
  ∃ (R : Type) (_ : CommRing R) (ξ : Sp R ⟶ X) (c : (Localization.Away (p : R))ˣ), IsOpenImmersion ξ ∧
    x ∈ Set.range ξ ∧ ∀ φ : R →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ) →
      ∀ ψ : Localization.Away (p : R) →+* ℂ_[p], ψ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
        ∀ κ ∈ K (spMap φ ≫ ξ), ‖ψ (c : Localization.Away (p : R)) - κ‖ < ‖κ‖

end GlobalTheory.FlatModel
