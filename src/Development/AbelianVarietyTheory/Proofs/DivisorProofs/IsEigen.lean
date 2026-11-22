import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenDescent

variable {X Y : Scheme.{0}}

def evU {Z : Scheme.{0}} (g : Z ⟶ X) {W : X.Opens} (hg : ∀ z, g z ∈ W) (f : Γ(X, W)ˣ) : Γ(Z, ⊤)ˣ :=
  res (fun z _ => hg z : (⊤ : Z.Opens) ≤ g ⁻¹ᵁ W) (pullU g W f)

def rat (π : X ⟶ Y) {V W : Y.Opens} (f : Γ(X, π ⁻¹ᵁ V)ˣ) (g : Γ(X, π ⁻¹ᵁ W)ˣ) :
    Γ(X, π ⁻¹ᵁ (V ⊓ W))ˣ :=
  res (π.preimage_mono inf_le_left) f * (res (π.preimage_mono inf_le_right) g)⁻¹

def Chart (π : X ⟶ Y) (E : ∀ V : Y.Opens, Γ(X, π ⁻¹ᵁ V)ˣ → Prop) : Type :=
  {p : (V : Y.Opens) × Γ(X, π ⁻¹ᵁ V)ˣ // E p.1 p.2}

open Classical in

def trans (π : X ⟶ Y) (E : ∀ V : Y.Opens, Γ(X, π ⁻¹ᵁ V)ˣ → Prop) (i j : Chart π E) :
    Γ(Y, i.1.1 ⊓ j.1.1)ˣ :=
  if h : ∃ u, pullU π _ u = rat π i.1.2 j.1.2 then h.choose else 1

end GlobalTheory.EigenDescent
