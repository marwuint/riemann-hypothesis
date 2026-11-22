import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffCurveOver
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentWeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin.CondTest

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem integral_of_mem_intAE {x : D.host.E} (hx : (1 : Af D.host.F) ⊗ₜ[D.host.F] x ∈ intAE D) :
    ∃ y : 𝓞 D.host.E, (y : D.host.E) = x := by
  have h : intAE D ≤ GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, y, rfl⟩
    exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral D.host.F ha ((FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩)
  exact (FractionalIdeal.mem_one_iff _).1 ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff D.host.F 1 x).1 (h hx))

end GlobalTheory.FinalJoin.CondTest
