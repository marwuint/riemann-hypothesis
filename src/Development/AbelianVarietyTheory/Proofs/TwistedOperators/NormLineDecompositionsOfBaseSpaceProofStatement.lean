import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLineDecompositionsOfBaseSpaceProof
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normLineDecompositionsOfBaseSpace_proof : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RecordDecSt D := by
  exact @GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec
