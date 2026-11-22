import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.UnitGlue

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

variable {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} {Xw : X.Opens} {K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]}
  (h : ∀ x : X, UnitChartAt p Xw K x)

def cR (x : X) : Type := Classical.choose (h x)

instance instCommRingCR (x : X) : CommRing (cR h x) := Classical.choose (Classical.choose_spec (h x))

def cξ (x : X) : Sp (cR h x) ⟶ X := Classical.choose (Classical.choose_spec (Classical.choose_spec (h x)))

def cu (x : X) : (Localization.Away (p : cR h x))ˣ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (h x))))

theorem c_spec (x : X) : IsOpenImmersion (cξ h x) ∧ x ∈ Set.range (cξ h x) ∧
    ∀ φ : cR h x →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ cξ h x) →
      ∀ ψ : Localization.Away (p : cR h x) →+* ℂ_[p], ψ.comp (algebraMap (cR h x) _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
        ∀ κ ∈ K (spMap φ ≫ cξ h x), ‖ψ (cu h x : Localization.Away (p : cR h x)) - κ‖ < ‖κ‖ :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (h x))))

instance instOpenImmCξ (x : X) : IsOpenImmersion (cξ h x) := (c_spec h x).1

end GlobalTheory.UnitGlue
