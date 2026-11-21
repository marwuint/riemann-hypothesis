import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section OneModel

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def AbLocusSmooth (Y : Model Xo c β) : Prop :=
  ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ SmoothOfRelativeDimension D.dim (U.ι ≫ Y.s)

end OneModel

def GoodPrime (l : Level H) (p : ℕ) : Prop :=
  Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) ∧ ¬ p ∣ l.M'

def SmoothnessLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, GoodPrime i.l p → AbLocusSmooth (Y i)

end GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth
