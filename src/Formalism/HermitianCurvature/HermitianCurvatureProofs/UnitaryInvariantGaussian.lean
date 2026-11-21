import Formalism.HermitianCurvature.StatementG

open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.G8

instance sigmaFinite_mu (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance

theorem psi_add (β x y : ℂ) : psi β (x + y) = psi β x * psi β y := by
  simp only [psi, mul_add, Complex.add_re, Complex.ofReal_add, Complex.exp_add]

end Formalism.FourierDecayAlt.P.G8

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
