import Formalism.LocalToGlobal.GlobalTheory.GL4.CTEqConjTranspose
import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrLoc
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.SuccessiveMinima.StatementMink
import Formalism.GL3MeanSquares.ConcavityEquidistribution

noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

variable {E : Type} [Field E] [NumberField E]

def incl (n : ℕ) : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) := (Algebra.linearMap (𝓞 E) E).compLeft (Fin n)

theorem incl_apply (n : ℕ) (m : Fin n → 𝓞 E) (i : Fin n) : incl n m i = (m i : E) := rfl

def psi {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) :=
  ((Matrix.mulVecLin G⁻¹).restrictScalars (𝓞 E)).comp (incl n)

theorem psi_apply {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (m : Fin n → 𝓞 E) : psi G m = G⁻¹ *ᵥ incl n m := rfl

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

end
