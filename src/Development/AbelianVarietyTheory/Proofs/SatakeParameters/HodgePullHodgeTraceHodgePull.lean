import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormResFormPullFormPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

open Opposite TensorProduct Limits GlobalTheory.Points

noncomputable section
namespace GlobalTheory.GalTrace

theorem preimage_le {Z Y W : Scheme.{0}} {c : Y ⟶ Z} {π : W ⟶ Z} {σ : W ⟶ Y} (hσ : σ ≫ c = π)
    (U : Z.Opens) : π ⁻¹ᵁ U ≤ σ ⁻¹ᵁ (c ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, hσ]

section Forms

variable {k : Type} [CommRing k] {Z Y W : Scheme.{0}} {s : Z ⟶ Sp k} {s' : Y ⟶ Sp k}
  {sW : W ⟶ Sp k} {c : Y ⟶ Z} {π : W ⟶ Z}

def liftPull {σ : W ⟶ Y} (hσ : σ ≫ c = π) (hσs : σ ≫ s' = sW) (j : ℕ) :
    (Scheme.Modules.pushforward c).obj (Omega s' j) ⟶
      (Scheme.Modules.pushforward π).obj (Omega sW j) :=
  (Scheme.Modules.pushforward c).map (omegaPull hσs j) ≫
    (Scheme.Modules.pushforwardComp σ c).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr hσ).hom.app _

theorem liftPull_app (hc : c ≫ s = s') (hπ : π ≫ s = sW) {σ : W ⟶ Y} (hσ : σ ≫ c = π)
    (hσs : σ ≫ s' = sW) (j : ℕ) (U : Z.Opens) (b : Sec s' (c ⁻¹ᵁ U)) (x : OmU s U j) :
    (liftPull hσ hσs j).app U (toOm s' j (c ⁻¹ᵁ U) (b • formPull hc U j x)) =
      toOm sW j (π ⁻¹ᵁ U) (Sec.res sW (preimage_le hσ U) (appSec s' sW σ (c ⁻¹ᵁ U) b) •
        formPull hπ U j x) := by
  change (Omega sW j).presheaf.map (homOfLE (preimage_le hσ U)).op
    ((omegaPull hσs j).val.app (op (c ⁻¹ᵁ U))
      ((toOmega s' j).app (op (c ⁻¹ᵁ U)) (b • formPull hc U j x))) = _
  rw [omegaPull_toOmega]
  refine (res_toOm sW j (preimage_le hσ U) (formPull hσs (c ⁻¹ᵁ U) j (b • formPull hc U j x))).trans
    (congrArg (toOm sW j (π ⁻¹ᵁ U)) ?_)
  have h : (σ ≫ c) ≫ s = sW := by rw [hσ, hπ]
  rw [formPull_smul hσs (c ⁻¹ᵁ U) b (formPull hc U j x), formRes_smul,
    formPull_formPull hc hσs h U j x]
  exact congrArg (_ • ·) (formRes_formPull_congr hσ h hπ U (preimage_le hσ U) j x)

theorem sum_app {F G : Z.Modules} {ι : Type} (R : Finset ι) (φ : ι → (F ⟶ G)) (U : Z.Opens)
    (y : Γ(F, U)) : (∑ r ∈ R, φ r).app U y = ∑ r ∈ R, (φ r).app U y := by
  classical
  induction R using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert a R ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app]
    exact congrArg ((φ a).app U y + ·) ih

variable [IsFinite c] [Etale c] (hc : c ≫ s = s') (hπ : π ≫ s = sW) {ι : Type} (R : Finset ι)
  {σ : ι → (W ⟶ Y)} (hσ : ∀ r, σ r ≫ c = π) (hσs : ∀ r, σ r ≫ s' = sW)

theorem omegaTrace_omegaPull
    (hF : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : Sec s' (c ⁻¹ᵁ U)),
      appSec s sW π U (secTrace s s' hU b) =
        ∑ r ∈ R, Sec.res sW (preimage_le (hσ r) U) (appSec s' sW (σ r) (c ⁻¹ᵁ U) b)) (j : ℕ) :
    omegaTrace hc j ≫ omegaPull hπ j = ∑ r ∈ R, liftPull (hσ r) (hσs r) j := by
  refine hom_ext_affine fun U hU y ↦ ?_
  obtain ⟨z, rfl⟩ := toOm_surjective (s := s') (j := j) (hU.preimage c) y
  refine formOm_induction (P := fun z ↦ (omegaTrace hc j ≫ omegaPull hπ j).app U
      (toOm s' j (c ⁻¹ᵁ U) z) = (∑ r ∈ R, liftPull (hσ r) (hσs r) j).app U
        (toOm s' j (c ⁻¹ᵁ U) z)) hc hU ?_ (fun y z hy hz ↦ ?_) (fun b x ↦ ?_) z
  · erw [map_zero, map_zero, map_zero]
  · erw [map_add, map_add, map_add]; exact congrArg₂ (· + ·) hy hz
  · refine Eq.trans ?_ (sum_app R _ U _).symm
    refine Eq.trans ?_ (Finset.sum_congr rfl fun r _ ↦
      liftPull_app hc hπ (hσ r) (hσs r) j U b x).symm
    rw [Scheme.Modules.Hom.comp_app]
    change (omegaPull hπ j).val.app (op U)
      ((omegaTrace hc j).app U (toOm s' j (c ⁻¹ᵁ U) (b • formPull hc U j x))) = _
    rw [omegaTrace_toOm_smul_formPull hc j hU, toOm_apply, omegaPull_toOmega, formPull_smul, hF,
      Finset.sum_smul]
    exact map_sum (toOm sW j (π ⁻¹ᵁ U)) _ _

theorem hodgePull_hodgeTrace (j : ℕ)
    (H : omegaTrace hc j ≫ omegaPull hπ j = ∑ r ∈ R, liftPull (hσ r) (hσs r) j) (q : ℕ)
    (x : hodgeH s' j q) :
    hodgePull hπ j q (hodgeTrace hc j q x) = ∑ r ∈ R, hodgePull (hσs r) j q x := by
  letI := algΓ s; letI := algΓ s'; letI := algΓ sW
  obtain ⟨y, rfl⟩ := (coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q).surjective x
  have e1 : hodgeTrace hc j q (coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q y) =
      cohOn.map k (omegaTrace hc j) ⊤ q y :=
    congrArg (cohOn.map k (omegaTrace hc j) ⊤ q)
      ((coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q).symm_apply_apply y)
  have e2 : ∀ φ : (Scheme.Modules.pushforward c).obj (Omega s' j) ⟶
      (Scheme.Modules.pushforward π).obj (Omega sW j),
      cohOn.pull (σ := RingHom.id k) (appTop_algebraMap hπ) (𝟙 _) (le_refl (π ⁻¹ᵁ ⊤)) q
        (cohOn.map k φ ⊤ q y) =
      cohOn.pull (σ := RingHom.id k) (appTop_algebraMap hπ) φ (le_refl (π ⁻¹ᵁ ⊤)) q y := fun φ ↦ by
    rw [cohOn.pull_map, Category.comp_id]
  have e4 := cohOn.pull_map (σ := RingHom.id k) (appTop_algebraMap hπ)
    (omegaPull hπ j) (omegaTrace hc j) (le_refl (π ⁻¹ᵁ ⊤)) (n := q) y
  have e5 : cohOn.map k (∑ r ∈ R, liftPull (hσ r) (hσs r) j) ⊤ q =
      ∑ r ∈ R, cohOn.map k (liftPull (hσ r) (hσs r) j) ⊤ q :=
    map_sum (cohOn.mapAddHom k _ _ ⊤ q) _ _
  rw [H, ← e2, e5, LinearMap.sum_apply, map_sum] at e4
  rw [e1]
  refine e4.trans (Finset.sum_congr rfl fun r _ ↦ (e2 _).trans ?_)
  have h : (σ r ≫ c) ≫ s = sW := by rw [hσ, hπ]
  have s2 := cohOn_pull_pull (appTop_algebraMap hc) (appTop_algebraMap (hσs r))
    (appTop_algebraMap h) (𝟙 _) (omegaPull (hσs r) j) (le_refl (c ⁻¹ᵁ ⊤)) (le_refl _) (le_refl _) q y
  have s3 := cohOn_pull_congr (hσ r) (appTop_algebraMap h) (appTop_algebraMap hπ)
    (G := Omega sW j) (𝟙 ((Scheme.Modules.pushforward c).obj (Omega s' j)) ≫
      (Scheme.Modules.pushforward c).map (omegaPull (hσs r) j) ≫
        (Scheme.Modules.pushforwardComp (σ r) c).hom.app _)
    (V := ⊤) (W := σ r ⁻¹ᵁ (c ⁻¹ᵁ ⊤)) (le_refl _) (fun _ _ ↦ trivial) q y
  have hm : liftPull (hσ r) (hσs r) j = (𝟙 ((Scheme.Modules.pushforward c).obj (Omega s' j)) ≫
      (Scheme.Modules.pushforward c).map (omegaPull (hσs r) j) ≫
        (Scheme.Modules.pushforwardComp (σ r) c).hom.app _) ≫
          (Scheme.Modules.pushforwardCongr (hσ r)).hom.app _ := by
    simp [liftPull]
  rw [hm]
  exact s3.symm.trans s2.symm

end Forms

end GlobalTheory.GalTrace
