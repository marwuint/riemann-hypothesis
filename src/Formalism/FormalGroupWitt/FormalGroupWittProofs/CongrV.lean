import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.CoeffV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.IntegralSubstVector
import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne

noncomputable section

universe u v w

namespace Formalism.FG.CongrVAux

open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux

section Norm

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}

def ofFun (g : (τ →₀ ℕ) → K) : MvPowerSeries τ K := g

theorem coeff_ofFun (g : (τ →₀ ℕ) → K) (e : τ →₀ ℕ) : coeff e (ofFun g) = g e := rfl

end Norm

end Formalism.FG.CongrVAux
