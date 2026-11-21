import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DetUpMatSub

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

structure IsClSub {n : ℕ} {ε : Fin n → Bool} (H : Set (Formalism.REAL.UJ ε)) : Prop where
  one_mem : (1 : Formalism.REAL.UJ ε) ∈ H
  mul_mem : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H
  inv_mem : ∀ x ∈ H, x⁻¹ ∈ H
  closed : IsClosed H

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
