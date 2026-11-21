import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType

noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
namespace GlobalTheory.UPoinc.UModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def valInt (t : UCTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* OO p :=
  (RatModel.valLoc t.y z₁ (specializes_of_eq t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem val_eq_valInt (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : t.val a = (valInt t a : PadicAlgCl p) :=
  RatModel.val_spMap_comp (OO p).subtype t.y (specializes_of_eq t.cen) (X₁.M.stalkEquiv z₁ a)

theorem norm_val_le (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖t.val a‖ ≤ 1 := by
  rw [val_eq_valInt]
  have h : Valued.v (valInt t a : PadicAlgCl p) ≤ 1 := (valInt t a).2
  exact_mod_cast h

end GlobalTheory.UPoinc.UModel
