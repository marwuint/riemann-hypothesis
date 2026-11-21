import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GSt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def leadMinor (Dw : Datum H) {n : ℕ} (K : Type) [CommRing K] (τ : E →+* ℂ) (s : ℕ) (hs : s ≤ Dw.mult τ) (cop : Fin s → Fin n) :
    MvPolynomial (LtN Dw n) K :=
  Matrix.det (Matrix.of fun (a i : Fin s) =>
    (MvPolynomial.X (⟨τ, (Fin.castLE hs a, cop i)⟩ : LtN Dw n) : MvPolynomial (LtN Dw n) K))

def minorProd (Dw : Datum H) {n : ℕ} (K : Type) [CommRing K] (typ : (E →+* ℂ) → Prop) (m : (E →+* ℂ) → ℕ → ℕ) (nb : ℕ)
    (cop : Fin nb → Fin n) : MvPolynomial (LtN Dw n) K :=
  open Classical in
  ∏ τ : E →+* ℂ, if typ τ then
    ∏ s ∈ Finset.range (Dw.mult τ + 1),
      (if h : s ≤ Dw.mult τ ∧ s ≤ nb then
        leadMinor Dw K τ s h.1 (fun i => cop (Fin.castLE h.2 i)) else 1) ^ m τ s
  else 1

def degOf (Dw : Datum H) (m : (E →+* ℂ) → ℕ → ℕ) : ℕ :=
  ∑ τ : E →+* ℂ, ∑ s ∈ Finset.range (Dw.mult τ + 1), s * m τ s

end GSt

open GSt

end Formalism.MainNotions.ModuliIntegralCharts.H1
