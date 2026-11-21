import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeModules
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangePlaces
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.SemiLocal

universe u

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω] [IsGalois L Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)
  (ιs : ∀ v : S, Ω →ₐ[F] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

omit [IsGalois L Ω] in

theorem coe_mackeyPlaceEquiv_eq (p : MackeyIndex (gsOpenSubgroup S hL) (gsFinFamily S ιs)) :
    (mackeyPlaceEquiv S hL ιs p : HeightOneSpectrum (𝓞 L)) = (gsLocalPlace hL ιs p.1 p.2.out).1 :=
  rfl

end GroundTheory.ProfCoh
