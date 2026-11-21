import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightedL2ConstMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cauchy
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Markov

namespace Formalism.FourierDecayAlt.P

theorem le_thetaRange_proof : Formalism.FourierDecayAlt.LE.ThetaRange := by
  intro ε σ x hε hσ hx
  simp only [LE.th]
  have hb : 0 < x / (x + ε) := by positivity
  exact ⟨Real.rpow_pos_of_pos hb σ, Real.rpow_le_one hb.le ((div_le_one (by linarith)).mpr (by linarith)) hσ⟩

theorem le_thetaSmooth_proof : Formalism.FourierDecayAlt.LE.ThetaSmooth := Formalism.FourierDecayAlt.P.LEx1.thetaSmooth

theorem cutoff_bound : Formalism.FourierDecayAlt.LE.CutBound := Formalism.FourierDecayAlt.P.LEx1.cutBound

theorem cutoff_theta : Formalism.FourierDecayAlt.LE.CutTheta := Formalism.FourierDecayAlt.P.LEx1.cutTheta

end Formalism.FourierDecayAlt.P
