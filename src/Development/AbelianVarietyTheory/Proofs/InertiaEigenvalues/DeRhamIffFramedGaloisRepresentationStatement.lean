import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamIffFramedGaloisRepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_iff_framed_galois_representation : FrameEx := by
  exact @GlobalTheory.PMon.FrameEquiv.frameEx
