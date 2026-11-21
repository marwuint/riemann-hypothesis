import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {m n : ℕ}

def IsUe (ε : Fin m → Bool) (X : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  Xᴴ * Matrix.diagonal (sgn ε) + Matrix.diagonal (sgn ε) * X = 0

def xyP (X : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) : PX m n :=
  ∑ c, C (if b then star (X a c) else X a c) * MvPolynomial.X (c, i, b)

def vfX (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : PX m n :=
  ∑ a, ∑ i, (xyP X a i false * pderiv (a, i, false) P + xyP X a i true * pderiv (a, i, true) P -
    C (c : ℂ) * (xyP X a i false * MvPolynomial.X (a, i, true) + xyP X a i true * MvPolynomial.X (a, i, false)) * P)

def zRe (ε : Fin m → Bool) (a b : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  (1 / 2 : ℂ) • (Matrix.single a b 1 - (sgn ε a * sgn ε b) • Matrix.single b a 1)

def zIm (ε : Fin m → Bool) (a b : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  (-(Complex.I / 2) : ℂ) • (Matrix.single a b 1 + (sgn ε a * sgn ε b) • Matrix.single b a 1)

end PositivityTheory.Rg.Sw.Glob
