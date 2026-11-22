import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualEmbBijective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def DualTopBasisChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T T₂ : Type) [Fintype T]
    [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b₂ : Module.Basis T₂ ℤ (dualLattice F))
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T₂) (dualIdeal b₂) i (fun _ => dualLine F b₂ hb₂) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb)

end

end GroundTheory.Heights₂.Heights
