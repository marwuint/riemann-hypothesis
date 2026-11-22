import Formalism.LocalToGlobal.Columns.Inputs
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.ColFormsLemmas
import Formalism.LocalToGlobal.Columns.CoefModAt
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.HermitianLatticesTheory MvPolynomial

theorem minkowskiBound_holds : MinkowskiBound := card_dvd_minkowskiNumber

end Formalism.L2.Col
