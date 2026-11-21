import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {T : Scheme.{0}}
  (t : SAB H T)

def LatPres {R : Type} [CommRing R] (x : Sp R ⟶ T) (kind : ℕ → Bool) (sc : ℕ → ℝ) {g M : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin M → Fin g → R) : Prop :=
  (∃ n : ℕ, n ≠ 0 ∧ ∀ i, Pi.single i (n : R) ∈ Submodule.span R (Set.range h)) ∧
  ∀ (p : ℕ) [Fact p.Prime] (φ : R →+* ↥(intO ℂ_[p])), ∃ δ : ℂ_[p], ‖δ‖ = (p : ℝ) ^ (-sc p) ∧
    ∀ (cf : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
      IsCombAtG t (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x)
        (fun i => spMap (dualMap ((intO ℂ_[p]).subtype.comp φ)) ≫ e i) cf w →
      (spMap (epsMul δ) ≫ w ∈ lat t p (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x) (kind p) ↔
        ∀ j, ‖∑ i, ((φ (h j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ ≤ 1)

end Tangent

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

abbrev LocAssign {X W : Scheme.{0}} (r : ℕ) (jB : W ⟶ X) (U : X.Opens) : Type 1 :=
  ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W), ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U → Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)

end Free

end GlobalTheory.ArLieBase

end
