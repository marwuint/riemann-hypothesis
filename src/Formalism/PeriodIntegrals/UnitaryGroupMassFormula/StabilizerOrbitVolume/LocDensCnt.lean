import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensCntL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnifVSpec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHL

noncomputable section

namespace PI.VolStabSW

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
open scoped TensorProduct

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {σ : E →ₐ[F] E} (A : AntiB F E σ)

theorem sigR_incl (e : E) : sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ ((1 : Fv F v) ⊗ₜ e) =
    (1 : Fv F v) ⊗ₜ σ e
  simp [Algebra.TensorProduct.map_tmul]

end Place

end PI.VolStabSW
