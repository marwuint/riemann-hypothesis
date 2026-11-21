import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueRuleOfRegular

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom.Vanish

open GlobalTheory.ShFam.Descent GlobalTheory.FlagTan GlobalTheory.AllWt GlobalTheory.Cartier

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

def FrameBC (Z : Model Xo c β) : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X)
    (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x),
      ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i

theorem FrameBC.at (hbc : FrameBC Z) {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') {x' : Sp R' ⟶ Z.X}
    (hx : x' = spMap ψ ≫ x) : ∃ g : EigFrame Z (ψ.comp φ) x', ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
  subst hx
  exact hbc R R' φ x f ψ

end GlobalTheory.CuspFrom.Vanish

namespace GlobalTheory.CuspFrom

end GlobalTheory.CuspFrom
