import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary

noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal ENNReal Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Height

variable {D : D7} (V : HSp D)

theorem isCompact_setOf_height_le (C : ℝ) : IsCompact {g : GA D V | height V g ≤ C} := by
  refine (GlobalTheory.AdelicU.isCompact_height_le (F := D.host.F) D.sp.cm.sig V.gram C.toNNReal).of_isClosed_subset
    (isClosed_le (continuous_height V) continuous_const) fun g hg => ?_
  exact NNReal.le_toNNReal_of_coe_le hg

variable {X : Type} [NormedAddCommGroup X]

end Height

end GlobalTheory.Grow
