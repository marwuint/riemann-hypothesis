import Formalism.MirabolicMackeyTheory.LocalConditionsWeighted
import Formalism.MirabolicMackeyTheory.MirabolicIsMackey
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsGlobalForm

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem enlarge_initial_lattice : EnlargeInitialLattice := by
  intro K _ _ _ Z _ _ _ _ _ w M Th1 Th hM h1 hT h1T hTM E r h W
  have a := (idxCutLe K Z w ⊤ W M Th hM hT hTM le_top).1
  have b := (idxCutLe K Z w ⊤ W Th Th1 hT h1 h1T le_top).1
  have c := (idxCutLe K Z w ⊤ W Th1 Th1 h1 h1 le_rfl le_top).1
  have d : cut W Th1 ≤ cut W Th := inf_le_inf_right _ h1T
  have e := idxMono K Z w W (cut W M) (cut W Th1) (cut W Th) a c b d
  have e' : (lix w (cut W M) (cut W Th) : ℝ) ≤ (lix w (cut W M) (cut W Th1) : ℝ) := by exact_mod_cast e
  exact le_trans e' (h W)

theorem twist_chain : TwChain := by
  intro K _ _ _ Z _ _ _ _ _ w W e A Th0 ThJ X₃ hA h0 hJ hle ε h
  have a := idxMono K Z w W A _ _ hA h0 hJ (Submodule.map_mono hle)
  have a' : (lix w A (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) ≤
      (lix w A (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) := by exact_mod_cast a
  linarith

theorem local_conditions_family : OnLocalJ := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th ThK Th0 ThJ X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 h4 h34 ε hTW d φ hinj hrng Mj Tj hMj hTj
  exact onLocal K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs σ hσ hsc hdata
    a E r ha hE hT0 h0 h3 h4 h34 ε
    (twist_chain K Z w _ e _ Th0 ThJ X₃ (idxCutLe K Z w ⊤ _ M Th hM hTh hle le_top).1 h0 hJ h0J ε hTW)
    d φ hinj hrng Mj Tj hMj hTj

theorem theta_identity : ThetaIdentity := by
  intro R X Y _ _ _ _ _ θ eX pr e hc hk Mt
  have key : ∀ m, θ (pr (eX m)) = e (θ m) := by
    intro m
    have h1 := hk (eX m) (LinearMap.mem_range_self eX m)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
    rw [← h1, ← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply]
  ext y
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨z, ⟨x, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩
    exact ⟨θ m, ⟨m, hm, rfl⟩, (key m).symm⟩
  · rintro ⟨z, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨pr (eX m), ⟨eX m, ⟨m, hm, rfl⟩, rfl⟩, key m⟩

theorem local_conditions_weighted : LocalConditionsWeighted := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ X₃ hM hTh1 hTh hThK h1le hle hFG hEig
    hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 X _ _ _ _ θ' eX pr Mt hc hk h4 h34 ε hTW d φ hinj hrng
    Mj Tj hMj hTj
  have hT0' := enlarge_initial_lattice K Z w M Th1 Th hM hTh1 hTh h1le hle (E : ℝ) r hT0
  have hc' : (θ'.restrictScalars (𝓞 K)) ∘ₗ (eX.restrictScalars (𝓞 K)) =
      (e.restrictScalars (𝓞 K)) ∘ₗ (θ'.restrictScalars (𝓞 K)) :=
    LinearMap.ext fun x => LinearMap.congr_fun hc x
  have hk' : ∀ x ∈ LinearMap.range (eX.restrictScalars (𝓞 K)),
      x - (pr.restrictScalars (𝓞 K)) x ∈ LinearMap.ker (θ'.restrictScalars (𝓞 K)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    exact LinearMap.mem_ker.2 (LinearMap.mem_ker.1 (hk _ (LinearMap.mem_range_self eX y)))
  have hid := theta_identity (𝓞 K) X Z (θ'.restrictScalars (𝓞 K)) (eX.restrictScalars (𝓞 K))
    (pr.restrictScalars (𝓞 K)) (e.restrictScalars (𝓞 K)) hc' hk' Mt
  exact local_conditions_family K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 ThJ X₃
    ((Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K))) hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0' h0 hJ h0J h3 h4 h34 ε hTW d φ hinj hrng Mj Tj hMj (hTj.trans hid)

end Formalism.EigenvalueLevelCeiling
