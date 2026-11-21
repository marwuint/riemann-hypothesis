import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstNormRealNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionWithDensities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonSummationDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonJointFirstReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalConditionsAndQuotientSplitting

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C

noncomputable section

theorem real_inputs_by_parts : C.RealInputsConcreteOfParts := by
  intro hEmb hEF hTD hLG hGram hWP hWave hPI hLift hBlock hE hCut E _ _ _ Wp Wq _ _ _ _ S jv H _ _ Vt C₄ hg1 hg2 hP hG hI hP1 hP23 hT hLE hPG Kr hK0 Th e
  exact ⟨hGram E Wp Wq S hP hG Kr hK0 Th e, hWP E Wp Wq S hG Kr hK0 Th e, hWave E Wp Wq S hG hI hP1 Kr hK0 Th e,
    hPI hEmb hEF hTD hLG E Wp Wq S hg1 hg2 hP hG hI Kr hK0 Th e, hLift E Wp Wq S hP23 Kr hK0 Th e,
    hBlock E Wp Wq S C₄ hT Kr hK0 Th e, hE E Wp Wq S jv hG hLE Kr hK0 Th e,
    hCut E Wp Wq S H Vt hPG Kr hK0 Th e⟩

theorem real_inputs_concrete_holds : C.RealInputsConcrete :=
  real_inputs_by_parts embedding_facts euclidean_frame trace_dual_alt
    lattice_facts_general gram_positive_semidefinite words_pos_of_parts wave_estimate_of_integral
    poisson_input_of_parts lift_estimate_of_base block_estimate_of_base level_zero_estimate_product
    cutoff_of_parts

end

end Formalism.FourierDecayAlt.P
