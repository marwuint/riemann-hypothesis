import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTheRecOfIsRec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength

noncomputable section

namespace GlobalTheory.ConjCoh

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.ContraPair Topology
open scoped TensorProduct

variable {E : Type} [Field E] {a : ℕ}

section Transport

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  [AddCommGroup M'] [Module ℂ M'] [Module ℝ M'] [IsScalarTower ℝ ℂ M']
  {κ : Kinf E a → Module.End ℂ M} {L : Lie E a →ₗ[ℝ] Module.End ℂ M}
  {κ' : Kinf E a → Module.End ℂ M'} {L' : Lie E a →ₗ[ℝ] Module.End ℂ M'}

def tr (σ : Herm E a →ₗ[ℝ] Herm E a) (T : M →ₗ[ℂ] M') {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) :
    Herm E a [⋀^Fin q]→ₗ[ℝ] M' :=
  (T.restrictScalars ℝ).compAlternatingMap (ω.compLinearMap σ)

theorem tr_apply (σ : Herm E a →ₗ[ℝ] Herm E a) (T : M →ₗ[ℂ] M') {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M)
    (X : Fin q → Herm E a) : tr σ T ω X = T (ω fun i => σ (X i)) := rfl

theorem isCochain_tr {σ : Herm E a →ₗ[ℝ] Herm E a} {s : Kinf E a → Kinf E a} {T : M →ₗ[ℂ] M'}
    (had : ∀ k X, σ (adHerm k X) = adHerm (s k) (σ X)) (hκ : ∀ k m, T (κ (s k) m) = κ' k (T m))
    {q : ℕ} {ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M} (hω : IsCochain κ ω) : IsCochain κ' (tr σ T ω) := fun k X => by
  rw [tr_apply, tr_apply, ← hκ, ← hω]
  simp only [had]

theorem dCo_tr {σ : Herm E a →ₗ[ℝ] Herm E a} {T : M →ₗ[ℂ] M'}
    (hL : ∀ X m, T (L (toL (σ X).1) m) = L' (toL X.1) (T m))
    {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : dCo L' (tr σ T ω) = tr σ T (dCo L ω) := by
  refine AlternatingMap.ext fun X => ?_
  rw [tr_apply, dCo_apply, dCo_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, hL, tr_apply]
  rfl

theorem tr_tr {σ : Herm E a →ₗ[ℝ] Herm E a} (hσ : ∀ X, σ (σ X) = X) (T : M ≃ₗ[ℂ] M')
    {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : tr σ T.symm.toLinearMap (tr σ T.toLinearMap ω) = ω := by
  refine AlternatingMap.ext fun X => ?_
  simp [tr_apply, hσ]

theorem tr_zero (σ : Herm E a →ₗ[ℝ] Herm E a) (T : M →ₗ[ℂ] M') {q : ℕ} :
    tr σ T (0 : Herm E a [⋀^Fin q]→ₗ[ℝ] M) = 0 :=
  AlternatingMap.ext fun X => by simp [tr_apply]

theorem hasCohomology_transport {σ : Herm E a →ₗ[ℝ] Herm E a} {s : Kinf E a → Kinf E a} (T : M ≃ₗ[ℂ] M')
    (hσ : ∀ X, σ (σ X) = X) (hs : ∀ k, s (s k) = k)
    (had : ∀ k X, σ (adHerm k X) = adHerm (s k) (σ X)) (hκ : ∀ k m, T (κ (s k) m) = κ' k (T m))
    (hL : ∀ X m, T (L (toL (σ X).1) m) = L' (toL X.1) (T m)) (H : HasCohomology κ L) : HasCohomology κ' L' := by
  have hκ' : ∀ k m, T.symm (κ' (s k) m) = κ k (T.symm m) := fun k m => by
    rw [T.symm_apply_eq]
    have := hκ (s k) (T.symm m)
    rw [hs, T.apply_symm_apply] at this
    exact this.symm
  have hL' : ∀ X m, T.symm (L' (toL (σ X).1) m) = L (toL X.1) (T.symm m) := fun X m => by
    rw [T.symm_apply_eq]
    have := hL (σ X) (T.symm m)
    rw [hσ, T.apply_symm_apply] at this
    exact this.symm
  rcases H with ⟨ω, h0, h1, h2⟩ | ⟨q, ω, h0, h1, h2⟩
  · refine Or.inl ⟨tr σ T.toLinearMap ω, isCochain_tr (T := T.toLinearMap) had hκ h0, ?_, fun h => h2 ?_⟩
    · rw [dCo_tr (L := L) (T := T.toLinearMap) hL, h1, tr_zero]
    · rw [← tr_tr hσ T ω, h, tr_zero]
  · refine Or.inr ⟨q, tr σ T.toLinearMap ω, isCochain_tr (T := T.toLinearMap) had hκ h0, ?_, fun η hη h => ?_⟩
    · rw [dCo_tr (L := L) (T := T.toLinearMap) hL, h1, tr_zero]
    · refine h2 (tr σ T.symm.toLinearMap η) (isCochain_tr (T := T.symm.toLinearMap) had hκ' hη) ?_
      rw [dCo_tr (L := L') (T := T.symm.toLinearMap) hL', h, tr_tr hσ]

end Transport

variable [NumberField E] [IsTotallyComplex E]

end GlobalTheory.ConjCoh

end

namespace GlobalTheory.ConjCoh

end GlobalTheory.ConjCoh
