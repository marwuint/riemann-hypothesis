import Mathlib
import GroundTheory.AutomorphicForms.WhittakerLocal
import GroundTheory.AutomorphicForms.AdelicGLn
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Filter Set

open scoped RestrictedProduct

namespace GroundTheory.Automorphic

namespace Whittaker

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem sigma_mem_integralGL {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} {g : GL (Fin n) F} (hg : g ∈ GLnLocal.integralGL F n) :
    sigma g ∈ GLnLocal.integralGL F n := by
  rw [GLnLocal.mem_integralGL_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [sigma_apply]; exact hg.1 _ _
  · rw [← sigma_inv, sigma_apply]; exact hg.2 _ _

variable (n : ℕ)

abbrev FinRes : Type _ := Πʳ v : HeightOneSpectrum (𝓞 K),
  [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n]

theorem sigma_mapsTo_integralGL : ∀ᶠ v in cofinite, MapsTo
    (sigma : GL (Fin n) ((id v : HeightOneSpectrum (𝓞 K)).adicCompletion K) → _)
    (GLnLocal.integralGL ((id v : HeightOneSpectrum (𝓞 K)).adicCompletion K) n :
      Set (GL (Fin n) ((id v : HeightOneSpectrum (𝓞 K)).adicCompletion K)))
    (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) :=
  Eventually.of_forall fun _ _ hg => sigma_mem_integralGL hg

def sigmaResFun : FinRes K n → FinRes K n :=
  RestrictedProduct.mapAlong _ _ id tendsto_id
    (fun v => (sigma : GL (Fin n) ((id v : HeightOneSpectrum (𝓞 K)).adicCompletion K) → _))
    (sigma_mapsTo_integralGL K n)

theorem continuous_sigmaResFun : Continuous (sigmaResFun K n) :=
  RestrictedProduct.mapAlong_continuous _ _ id tendsto_id _ (sigma_mapsTo_integralGL K n)
    fun _ => continuous_sigma

def sigmaRes : FinRes K n ≃ₜ FinRes K n where
  toFun := sigmaResFun K n
  invFun := sigmaResFun K n
  left_inv _ := RestrictedProduct.ext _ _ fun _ => sigma_sigma _
  right_inv _ := RestrictedProduct.ext _ _ fun _ => sigma_sigma _
  continuous_toFun := continuous_sigmaResFun K n
  continuous_invFun := continuous_sigmaResFun K n

@[simp] theorem sigmaRes_apply (x : FinRes K n) (v : HeightOneSpectrum (𝓞 K)) :
    sigmaRes K n x v = sigma (x v) := rfl

variable [DecidableEq (HeightOneSpectrum (𝓞 K))]

end

end Whittaker

end GroundTheory.Automorphic
