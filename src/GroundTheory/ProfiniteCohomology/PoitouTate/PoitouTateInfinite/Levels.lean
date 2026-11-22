import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.Restrict
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerFrob
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSUnram
import GroundTheory.ProfiniteCohomology.CupProducts.Pairing
import GroundTheory.LocalFields.WildInertia

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Unramified

open GroundTheory.LocalField

variable (T : Set (HeightOneSpectrum (𝓞 K.1))) {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

end Unramified

end

end GroundTheory.ProfCoh
