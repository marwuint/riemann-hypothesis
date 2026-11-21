import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.UnitaryTwist

def normRpow (r : ℝ) : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((‖(z : ℂ)‖ ^ r : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (norm_pos_iff.2 z.ne_zero) r).ne')
  map_one' := by ext; simp
  map_mul' z w := by
    ext
    simp [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

theorem normRpow_val (r : ℝ) (z : ℂˣ) : ((normRpow r z : ℂˣ) : ℂ) = ((‖(z : ℂ)‖ ^ r : ℝ) : ℂ) := rfl

end GlobalTheory.UnitaryTwist
