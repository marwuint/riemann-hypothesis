import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def projSpaceHilb (N : ℕ) (t : ℤ) : ℤ :=
  if 0 ≤ t then (((t.toNat + N).choose N : ℕ) : ℤ) else 0

def HilbAddBlock.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)) (N : ℕ) (m : Option K → ℤ),
    hilbFn (addBlockPrime N I) m = hilbFn I (fun k => m (some k)) * projSpaceHilb N (m none)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
