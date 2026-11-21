import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing

open Formalism.L2.Pj Formalism.L2.PjFree NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {c c' : Coeff l}

def incl (h : c.F ≤ c'.F) : c.F →+* c'.F := (IntermediateField.inclusion h).toRingHom

def Res (_h : c.F ≤ c'.F) (S : Type) : Type := S

instance (h : c.F ≤ c'.F) (S : Type) [CommRing S] : CommRing (Res h S) := inferInstanceAs (CommRing S)

instance (h : c.F ≤ c'.F) (S : Type) [CommRing S] [Algebra c'.F S] : Algebra c.F (Res h S) :=
  ((algebraMap c'.F S).comp (incl h)).toAlgebra

def unRes {h : c.F ≤ c'.F} {S : Type} [CommRing S] : Res h S ≃+* S := RingEquiv.refl S

variable {Xo : Moduli Dw l}

def ptDown (h : c.F ≤ c'.F) {S : Type} [CommRing S] [Algebra c'.F S] (y : FrPt Xo c' S) :
    FrPt Xo c (Res h S) where
  x := y.x
  x_over := y.x_over
  u := y.u
  tan := y.tan
  eig := y.eig
  basis := y.basis
  s := y.s
  gen := y.gen

def ptUp (h : c.F ≤ c'.F) {S : Type} [CommRing S] [Algebra c'.F S] (y : FrPt Xo c (Res h S)) :
    FrPt Xo c' S where
  x := y.x
  x_over := y.x_over
  u := y.u
  tan := y.tan
  eig := y.eig
  basis := y.basis
  s := y.s
  gen := y.gen

variable {r : ℕ}

def ruleUp (h : c.F ≤ c'.F) : Rul Xo c →ₛₗ[incl h] Rul Xo c' where
  toFun f := fun p y => unRes (evR Xo c f (ptDown h y))
  map_add' f g := by
    funext p y
    exact evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (ptDown h y)
  map_smul' a f := by
    funext p y
    have e := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) a f (ptDown h y)
    show _ = incl h a • (unRes (evR Xo c f (ptDown h y)) : p.R)
    exact e.trans (Algebra.smul_def (incl h a) (unRes (evR Xo c f (ptDown h y)) : p.R)).symm

variable (Xo)

end GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing
