import Formalism.MahlerMeasure.FinalM
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt

namespace Formalism.GM.Top
open Formalism.GM
theorem gamDeg : M.GamDeg := gamma_degree_bound
theorem gamLead : M.GamLead := gamma_leading_term
end Formalism.GM.Top
