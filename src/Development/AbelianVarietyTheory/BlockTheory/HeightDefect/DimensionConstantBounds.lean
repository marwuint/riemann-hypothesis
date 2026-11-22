import Mathlib
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.SharpRestriction.Divisibility.WeightFamilies

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DimensionConstantBounds

open Formalism.BasicNotions Formalism.MainNotions.WeightFamilies NumberField

def Z {D : D7} (L : SizeData₂ D) : ℝ := (D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L

def lrd (D : D7) : ℝ := Real.log D.host.rdE

def q (D : D7) : ℕ := min (D.host.g 0) (D.host.g 1)

def r1 : ℕ := 5

def g0 (D : D7) : ℕ := 2 * r1 ^ 4 * D.R.r

def dimX (D : D7) (j : ℕ) : ℕ := D.R.f * (D.R.sigW j).1 * (D.R.sigW j).2

def degF {D : D7} {j : ℕ} (w : Wt D j) : ℕ := ∑ τ, ((∑ i, w.aP τ i) + ∑ i, w.aM τ i)

def LamStar (D : D7) : ℝ :=
  Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
    Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * (D.host.q : ℝ) * (D.host.d : ℝ))

def PN {D : D7} (L : SizeData₂ D) : ℝ := 2 * L.sc.L + LamStar D + 4

def n0 (D : D7) (j : ℕ) : ℕ := D.R.r + 2 * g0 D * (dimX D j + 1)

def PO {D : D7} (L : SizeData₂ D) : ℝ :=
  19 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L + 198 * (D.R.f : ℝ) ^ 2 * L.sc.L

theorem Z_eq {D : D7} (L : SizeData₂ D) : Z L = zBase L := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.DimensionConstantBounds

end
