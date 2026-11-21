import Formalism.LocalToGlobal.Columns.RecLevelCls

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

section Ad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem til_tmv_int_of_iA {a : E} (h : iA F E a ∈ Formalism.L2.Herm.intAf F E) : ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = a := by
  have h1 : (fun _ : Fin 1 => a) ∈ Formalism.UG.CS.globLat (F := F) (1 : GL (Fin 1) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E 1) := by
    rw [mem_globLat]
    intro i
    rw [pullV_one]
    exact h
  rw [globLat_one_std, mem_stdLat] at h1
  exact h1 0

variable {n : ℕ} [NeZero n] (ST SG : Finset (Pl E))

end Ad

end Formalism.L2.Col
