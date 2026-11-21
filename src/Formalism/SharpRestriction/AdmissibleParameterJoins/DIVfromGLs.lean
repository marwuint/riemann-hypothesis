import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLl
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLm
import Formalism.SharpRestriction.GlobalSchurBounds.WachTwistLocalTheory
import Formalism.SharpRestriction.GlobalSchurBounds.JointsF
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.MainNotions.WeightDegreeSizes

variable {D : D7} {L : SizeData₂ D}

theorem level_primes_ne_type_primes (D : D7) : LevelPrimeNotTypePrime D :=
  fun u i => (D.T_ne_g u i).symm

theorem sizeData_at_level_primes {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef)
    (hE : L.EDef X K c) : LevelPrimeSizes D L :=
  sizeData_at_level_primes_of_defs P hF hE (level_primes_ne_type_primes D)

end Formalism.MainNotions.J

end
