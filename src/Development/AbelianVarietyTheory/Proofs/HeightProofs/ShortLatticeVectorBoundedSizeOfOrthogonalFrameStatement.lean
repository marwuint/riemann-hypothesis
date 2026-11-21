import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ShortLatticeVectorBoundedSizeOfOrthogonalFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortLatticeVectorBoundedSize_of_orthogonalFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E → ShortSmall E := by
  exact @GlobalTheory.SmoothForms.Short.shortSmall
