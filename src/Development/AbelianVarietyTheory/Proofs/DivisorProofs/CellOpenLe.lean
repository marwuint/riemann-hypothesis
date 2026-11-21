import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.Cell

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

section Mat

variable {R : Type} [CommRing R] {m : ℕ}

abbrev Above (m : ℕ) : Type := {p : Fin m × Fin m // p.1 < p.2}

def IsLowInv (L : Matrix (Fin m) (Fin m) R) : Prop := (∀ i j, i < j → L i j = 0) ∧ ∀ i, IsUnit (L i i)

def upMat (a : Above m → R) : Matrix (Fin m) (Fin m) R := fun i j =>
  if h : i < j then a ⟨(i, j), h⟩ else if i = j then 1 else 0

def InCell (M : Matrix (Fin m) (Fin m) R) (w : Equiv.Perm (Fin m)) (a : Above m → R) : Prop :=
  ∃ L, IsLowInv L ∧ M.submatrix id w = L * upMat a

end Mat

end GlobalTheory.ShFam.Cell
