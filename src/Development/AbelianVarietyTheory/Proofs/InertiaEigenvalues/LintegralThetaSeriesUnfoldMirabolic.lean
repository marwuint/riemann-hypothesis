import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainIUnion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open MeasureTheory GlobalTheory.CuspRep
open scoped ENNReal Matrix

namespace GlobalTheory.ThetaUnfold

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

open NumberField Matrix GlobalTheory.MirTower in

theorem mem_mirU_pred {K : Type} [Field K] {a : ℕ} (ha : 0 < a) (γ : GL (Fin a) K) :
    γ ∈ mirU K a (a - 1) ↔ ∀ j, γ.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ j =
      if j = ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ then 1 else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  exact mem_mirU_last

open NumberField Matrix GlobalTheory.MirTower in

theorem lintegral_theta_unfold : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕P μ → ∀ F : GA E a → (Fin a → Ad E) → ℝ≥0∞, (∀ v : Fin a → E, Measurable fun g : GA E a => F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)) → (∀ (γ : GL (Fin a) E) g y, F (ratGL E a γ * g) y = F g y) → ∫⁻ g in 𝓕, ∑' ξ : {v : Fin a → E // v ≠ 0}, F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ.1 i)) g.val) ∂μ = ∫⁻ g in 𝓕P, F g (g.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩) ∂μ := by
  intro E _ _ a ha μ _ 𝓕 𝓕P h𝓕 h𝓕P F hm hF
  set l : Fin a := ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩
  have hv : (Pi.single l 1 : Fin a → E) ≠ 0 := fun h0 => by simpa using congrFun h0 l
  have hP' : ∀ γ : GL (Fin a) E, γ ∈ mirU E a (a - 1) ↔ (Pi.single l 1 : Fin a → E) ᵥ* γ.val = Pi.single l 1 :=
    fun γ => by
      rw [mem_mirU_pred ha, Matrix.single_one_vecMul, funext_iff]
      simp only [Pi.single_apply, Matrix.row]
      rfl
  have he : algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin a → E) = (Pi.single l 1 : Fin a → Ad E) := by
    funext j
    simp only [Function.comp_apply, Pi.single_apply]
    split_ifs <;> simp
  have := lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕P F hF (hm _).aemeasurable
  simp only [he, Matrix.single_one_vecMul] at this
  exact this

end GlobalTheory.ThetaUnfold
