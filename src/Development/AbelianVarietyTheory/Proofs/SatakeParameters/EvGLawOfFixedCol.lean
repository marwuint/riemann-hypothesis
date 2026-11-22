import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.ChainTw
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker MvPolynomial

namespace GlobalTheory.KerJ

theorem ufGL_val {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = LinearMap.toMatrix' γ.1.toLinearMap := by
  simp [ufGL, toGLm]
  rfl

end GlobalTheory.KerJ
