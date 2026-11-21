import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.Quadratic
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Module

namespace GroundTheory.Global

namespace Quadratic

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

def conj : Gal(K/ℚ) :=
  (exists_ne_one_of_card_eq_two (card_gal K)).choose

abbrev conjRing : 𝓞 K →+* 𝓞 K :=
  MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K) (conj K)

theorem coe_conjRing (x : 𝓞 K) : ((conjRing K x : 𝓞 K) : K) = conj K (x : K) :=
  rfl

end Quadratic

end GroundTheory.Global
