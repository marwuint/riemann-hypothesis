import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalAnisotropicFrameBoundedCM
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalAnisotropicFrame_bounded_CM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E := by
  exact @GlobalTheory.SmoothForms.frameSmall
