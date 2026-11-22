import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.UnfoldAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Unimod
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective

noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

section Inst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

instance nontrivAF : Nontrivial (AF F) := by
  haveI : Nontrivial (Ainf F) := by
    first
    | exact inferInstance
    | (haveI : Nonempty (NumberField.InfinitePlace F) := inferInstance; exact Pi.nontrivial)
  first
  | exact inferInstance
  | exact inferInstanceAs (Nontrivial (Ainf F × Af F))
  | exact (Prod.nontrivial_left : Nontrivial (Ainf F × Af F))

end Inst

end PI.VolStabW
