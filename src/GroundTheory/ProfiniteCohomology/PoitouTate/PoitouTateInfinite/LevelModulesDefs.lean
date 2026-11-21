import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.Descent
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.Levels
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDecomp
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}

theorem isOpen_ker_ρ {k G : Type*} [CommRing k] [Group G] [TopologicalSpace G] (A : Rep k G) [IsDiscreteRep A]
    [Finite A] : IsOpen ((A.ρ.ker : Subgroup G) : Set G) := by
  have e : ((A.ρ.ker : Subgroup G) : Set G) = ⋂ a : A, (stabilizer A.ρ a : Set G) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter]
    constructor
    · intro h a
      change A.ρ g a = a
      rw [h, Module.End.one_apply]
    · intro h
      exact LinearMap.ext fun a => h a
  rw [e]
  exact isOpen_iInter_of_finite fun a => isOpen_stabilizer A a

variable {T : Set (HeightOneSpectrum (𝓞 K.1))} (h : T ⊆ S)

theorem gsResCont_surjective : Function.Surjective (gsResCont (Ω := ℚ̄) h) := fun τ => by
  obtain ⟨σ, hσ⟩ := gsRes_surjective (Ω := ℚ̄) h τ
  exact ⟨σ, by rw [gsResCont_apply]; exact hσ⟩

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
  (hM : ∀ g, gsResCont (Ω := ℚ̄) h g = 1 → M.ρ g = 1)

abbrev levelModule : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ T) :=
  descendRep (gsResCont (Ω := ℚ̄) h) (gsResCont_surjective h) M hM

theorem isQuotientMap_gsResCont : Topology.IsQuotientMap (gsResCont (Ω := ℚ̄) h) :=
  (gsResCont (Ω := ℚ̄) h).continuous.isClosedMap.isQuotientMap (gsResCont (Ω := ℚ̄) h).continuous
    (gsResCont_surjective h)

instance isDiscreteRep_levelModule [IsDiscreteRep M] : IsDiscreteRep (levelModule h M hM) :=
  isDiscreteRep_descendRep _ (gsResCont_surjective h) M hM (isQuotientMap_gsResCont h)

end

end GroundTheory.ProfCoh
