import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

def IsEigTan {K : Type} [CommRing K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (τ : E →+* ℂ)
    (w : Sp (DualNumber K) ⟶ Z.t.G.left) : Prop :=
  IsTanAtG Z.t x w ∧ ∀ a : 𝓞 E, w ≫ (Z.t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ w

def IsEigBasis {K : Type} [CommRing K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (τ : E →+* ℂ) {m : ℕ}
    (u : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)) : Prop :=
  (∀ i, IsEigTan Z φ x τ (u i)) ∧ ∀ w, IsEigTan Z φ x τ w → ∃! a : Fin m → K, IsCombAtG Z.t x u a w

end Free

end GlobalTheory.ArLieBase

end
