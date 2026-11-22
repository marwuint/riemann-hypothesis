import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoPolish

noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct RestrictedProduct

namespace RestrictedProductGluing

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {M a d : ℕ} (b : Module.Basis (Fin d) F E)

def mkAf (x : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in cofinite, x v ∈ v.adicCompletionIntegers F) : Af F :=
  (⟨x, h⟩ : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

omit [FiniteDimensional F E] in
theorem evalV_mkAf (x : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in cofinite, x v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (mkAf x h) = x v := rfl

end RestrictedProductGluing

end PI.VolStabW
