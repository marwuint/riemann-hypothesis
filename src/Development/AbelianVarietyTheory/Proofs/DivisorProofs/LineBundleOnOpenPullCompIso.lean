import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundlePullOfIsLineBundleOnOpen

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem isOn_pull_comp : ∀ (X Z Z' : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X) (s : Z' ⟶ Z),
    IsOn W L → (∀ z, r z ∈ W) → LBIso ((L.pull r).pull s) (L.pull (s ≫ r)) := by
  intro X Z Z' W L r s hL hr
  have h : (L.pull (s ≫ r)).IsLB := _root_.GlobalTheory.PicGlue.pull_isLB_of_isOn X Z' W L (s ≫ r) hL fun z ↦ by
    simpa using hr (s z)
  exact iso_of_chart h (chartPullLinComb L r (fun _ : PUnit => s) (fun _ => s ≫ r) (fun _ => 1) (𝟙 _)
    fun _ => (Category.id_comp _).symm)

end GlobalTheory.PicGlue
