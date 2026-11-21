import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericNoetherNormalisation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProofSimp

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Polynomial MvPolynomial Ideal Nat RingHom List

namespace GenericNoetherNormalisation

universe u

theorem proof : GenericNoetherNormalisation.Statement.{u} :=
  _root_.UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof

end GenericNoetherNormalisation

end GroundTheory.Heights₂.Heights
