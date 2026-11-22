import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfAbsoluteConvergence
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
import Mathlib
import Formalism.LatticeRigidity.StatementA
import Formalism.LatticeRigidity.StatementC
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (decExp)

def DistTri : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g k : Formalism.REAL.UJ ε), cartanDistance ε (g * k) ≤ cartanDistance ε g + cartanDistance ε k

end Formalism.MainNotions.LeviCoordinates

end
