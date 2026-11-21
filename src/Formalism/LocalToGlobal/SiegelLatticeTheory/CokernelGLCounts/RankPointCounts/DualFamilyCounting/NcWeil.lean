import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes

noncomputable section

namespace Formalism.L2.SG.Pf.NcWeil

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.UnusedSlot34 Formalism.L2.SG.Volumes NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def VolStabW : Prop :=
  IsHermND σ J → ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j),
    (gramE σ J X0).det ≠ 0 → VolStabAt F E σ M J X0 hT

end Ext

end Formalism.L2.SG.Pf.NcWeil
