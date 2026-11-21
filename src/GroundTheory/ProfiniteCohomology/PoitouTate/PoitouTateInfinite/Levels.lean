import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.Restrict
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerFrob
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSUnram
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Ramified
import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
import GroundTheory.ProfiniteCohomology.Procyclic
import GroundTheory.ProfiniteCohomology.CupProducts.Functoriality
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

theorem inertiaGroup_le_ker_decompHomS (hv : v ∉ T) :
    inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) ≤
      (decompHomS (v.adicCompletion K.1) T ι).ker := by
  intro g hg
  refine MonoidHom.mem_ker.2 (decompHomS_eq_one_of_unramifiedDegree_eq_one T ι hv g ?_)
  rw [← MonoidHom.mem_ker, ker_unramifiedDegree]
  exact hg

def decompHomSUnram (hv : v ∉ T) :
    Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ⧸
        inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) →ₜ*
      galUnramifiedOutside K.1 ℚ̄ T :=
  ⟨QuotientGroup.lift _ (decompHomS (v.adicCompletion K.1) T ι) (inertiaGroup_le_ker_decompHomS T ι hv),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
      (continuous_decompHomS (Kv := v.adicCompletion K.1) T ι)⟩

theorem decompHomSUnram_mk (hv : v ∉ T) (g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    decompHomSUnram T ι hv (g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ⧸
      inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) =
      decompHomS (v.adicCompletion K.1) T ι g :=
  rfl

end Unramified

end

end GroundTheory.ProfCoh
