import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthonormalBasesMemUnitaryLieAlgebra
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalBases_mem_unitaryLieAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε) ∧ ∀ b, pB ε b ∈ lieSet ε := by
  exact @GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet
