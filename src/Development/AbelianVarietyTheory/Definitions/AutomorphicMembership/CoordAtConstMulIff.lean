import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier
open GlobalTheory.ShFam.Descent GlobalTheory.FlatLine

namespace GlobalTheory.ShFam.Pad

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Frame

variable (Z : Model Xo c β) {R : Type} [CommRing R] [Algebra c.F R] (P : FrPt Xo c R)

def frameOf : EigFrame Z (algebraMap c.F R) (GlobalTheory.AllWt.ptF P ≫ Z.j) := (exists_tie_frame P rfl).choose

variable {Z P}

end Frame

variable {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

def CoordAt {k : Type} [Field k] [Algebra c.F k] (P : FrPt Xo c k) (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : k) : Prop :=
  ∃ p : Sp k ⟶ Y.Y.X, p ≫ Y.π = GlobalTheory.AllWt.ptF P ≫ Z.jQ ∧ IsCoord Y p (frameOf Z P) n σ a

def CoordAtC {ι : c.F →+* ℂ} (P : FrPt Xo c (CAt ι)) (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : ℂ) : Prop :=
  letI := ι.toAlgebra; CoordAt (k := ℂ) Y P n σ a

variable {Y}

variable {r : ℕ}

end Free

end GlobalTheory.ShFam.Pad
