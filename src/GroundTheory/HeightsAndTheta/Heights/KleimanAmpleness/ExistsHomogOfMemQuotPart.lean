import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellResMemLocPart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cellMon cellRes locPart mIdealOver mConeMapOver chartRingOver quotPart)

noncomputable section

namespace CechPointEval

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Eval

variable {Ω : Type} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)

theorem aeval_eq_zero_of_mem {f : MRingOver F ι} (hf : f ∈ mIdealOver F y) : aeval y f = 0 := by
  have h : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMapOver F y).toRingHom =
      (aeval y : MRingOver F ι →ₐ[F] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMapOver, MvPolynomial.algebraMap_apply]
    · intro p
      simp [mConeMapOver]
  have h2 := RingHom.congr_fun h f
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
  rw [← h2, show mConeMapOver F y f = 0 from (RingHom.mem_ker).mp hf, map_zero]

def ev0 : (MRingOver F ι ⧸ mIdealOver F y) →ₐ[F] Ω :=
  Ideal.Quotient.liftₐ (mIdealOver F y) (aeval y) (fun _ hf => aeval_eq_zero_of_mem y hf)

theorem evalAtPoint_mk (p : MRingOver F ι) : ev0 y (Ideal.Quotient.mk (mIdealOver F y) p) = aeval y p := rfl

variable {y}

variable (y)

end Eval

variable {Ω : Type} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)

end CechPointEval

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
