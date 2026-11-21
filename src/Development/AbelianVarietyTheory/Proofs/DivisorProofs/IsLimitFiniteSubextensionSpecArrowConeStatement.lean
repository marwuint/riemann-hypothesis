import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitFiniteSubextensionSpecArrowCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLimit_finiteSubextensionSpecArrowCone : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω], IsColimit (GlobalTheory.SepCech.ringCocone K Ω) → Nonempty (IsLimit (Arrow.leftFunc.mapCone (GlobalTheory.SepCech.arrCone K Ω))) := by
  exact @GlobalTheory.SepCech.isLimit_leftFunc_arrCone
