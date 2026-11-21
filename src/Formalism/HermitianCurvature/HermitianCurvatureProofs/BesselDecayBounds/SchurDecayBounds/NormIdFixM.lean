import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdFix
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.IsHaarOnUWsetOfIsHaarOnOfUnivEqOne

namespace PI.WBL.NIS

theorem measSideP : MeasSideP := by
  intro k r z u Wp _ _ _ π μW μN hz hT hπ hW hN
  exact Formalism.MainNotions.MeasFS.measF_side hz hT hπ hW hN

end PI.WBL.NIS
