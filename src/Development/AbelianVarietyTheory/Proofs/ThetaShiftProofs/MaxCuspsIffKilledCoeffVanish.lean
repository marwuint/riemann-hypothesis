import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SublatticeCoefficients
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspKilledCoefficientEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspMemCuspFormsOfKilledCoefZero

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

namespace GlobalTheory

theorem maxCusps_iff_killed_coeff_vanish : MaxCuspsStatement := by
  intro E _ _ _ r ρ X hspan hbas la hχ c P hP
  exact ⟨fun h => _root_.GlobalTheory.MaxCuspKilled.coefFn_eq_zero_of_killed E r ρ X hbas la hχ c P h,
    fun h => _root_.GlobalTheory.maxCusps_mem_SSgt_of_coef_eq_zero E r ρ X hspan hbas la hχ c P hP h⟩

end GlobalTheory
