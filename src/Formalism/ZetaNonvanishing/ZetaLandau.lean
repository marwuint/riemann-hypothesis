import Formalism.StatementU
import Formalism.ZetaNonvanishing.MeasurableGchi
import Formalism.ZetaNonvanishing.MellinSgen

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

open ArithmeticFunction

def linZ (s : ℂ) : ℂ := -1 + (1 + (Real.eulerMascheroniConstant : ℂ)) * s

def nZ (s : ℂ) : ℂ := -(deriv riemannZeta₁ s / riemannZeta₁ s) + linZ s

def HZ (ε C θ : ℝ) (x : ℝ) : ℝ := ε * Gz x + C * x ^ θ

end Formalism
