import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryStabiliserEmbeddingNormLaws
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_stabiliser_embedding_norm_laws : EmbLaws := by
  exact @GlobalTheory.SepReal.embLaws
