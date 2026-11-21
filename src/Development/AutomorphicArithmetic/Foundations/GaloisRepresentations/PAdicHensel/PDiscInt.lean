import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.DatExOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.DatumToG
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PDiscInt

noncomputable section

open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.G1

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pDiscInt : DiscInt :=
  _root_.UpperTheory.Reformulated.B.Qk39.pDiscInt

end UpperTheory.Gal.G1
