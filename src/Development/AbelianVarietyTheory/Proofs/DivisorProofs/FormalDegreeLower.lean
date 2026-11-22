import Mathlib
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BottomMinor
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.EulerProductSatake

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open Formalism.MainNotions.SchurIrreducible (IrrGK)
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts (delta wtK wtExt wtH IsLowestType IsKIntw)
open GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors (Place eulerProd dPart quadSign SatakeBound)
open scoped TensorProduct

namespace GlobalTheory.BlockSizes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def rowsP (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).1) : ℕ := ⌊DV.aPlusQ D j τ i⌋₊

def rowsM (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).2) : ℕ :=
  ⌊DV.aMinusQ D j τ ((D.R.sigW j).2 - 1 - i)⌋₊

variable {D : D7} (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)

def WindowsLe (L : SizeData₂ D) : Prop := L.etaSz ≤ L.sc.b ∧ L.Sc ≤ L.sc.b

end GlobalTheory.BlockSizes

end
