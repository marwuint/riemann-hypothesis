import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial

namespace Formalism.HermitianLatticeCounting.Final.S6

theorem nFJZero : Formalism.HermitianLatticeCounting.S6.NFJZero := Formalism.HermitianLatticeCounting.P.normalFormZero

theorem normalForm : Formalism.HermitianLatticeCounting.S6.NormalForm := Formalism.HermitianLatticeCounting.P.existsNormalForm

theorem normSgBound : Formalism.HermitianLatticeCounting.S6.NormSgBound := Formalism.HermitianLatticeCounting.P.norm_singular_value_bound

theorem finalSum : Formalism.HermitianLatticeCounting.S6.FinalSum := Formalism.HermitianLatticeCounting.P.final_sum_bound

end Formalism.HermitianLatticeCounting.Final.S6
