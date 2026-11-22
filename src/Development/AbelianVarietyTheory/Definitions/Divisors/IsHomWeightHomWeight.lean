import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CxPts
open GlobalTheory.AllWt (secZ exOf wtOf lieFacZ modelWt homN)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag kap)
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {r : ℕ}

variable {X : FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

variable {U} {σ : c.F →+* ℂ} {la a b : AllWt.Weight Dw}

variable {M x} {y : CxPts M.str σ}

variable (U x) (ω : CanId M)

instance secondCountable_modif (σ : c.F →+* ℂ) : SecondCountableTopology (CxPts M.str σ) :=
  secondCountableTopology_of_isProjOver σ M.proj

variable {U x}

variable {ω}

end GlobalTheory.CompHS
