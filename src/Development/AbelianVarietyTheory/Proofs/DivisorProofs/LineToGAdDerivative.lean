import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixOneParameterGroupEqExpOfContinuous

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

open scoped TensorProduct Matrix ContDiff

namespace GlobalTheory.LineDerSum

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem skew_of_exp_unitary {n : ℕ} (A Z : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ * A * NormedSpace.exp (t • Z) = A) : Zᴴ * A + A * Z = 0 := by
  have h1 : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ = NormedSpace.exp (t • Zᴴ) := fun t => by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial]
  have hd := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Zᴴ (0 : ℝ)).mul_const A).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ))
  have he : ((fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A) * fun t : ℝ => NormedSpace.exp (t • Z)) = fun _ => A :=
    funext fun t => by rw [Pi.mul_apply, ← h1, h]
  simpa using hd.unique ((hasDerivAt_const (0 : ℝ) A).congr_of_eventuallyEq (.of_forall (congrFun he)))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isRealLine_component (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (δ : ℝ → GAd σ J)
    (hc : Continuous δ) (h0 : δ 0 = 1) (hm : ∀ s t, δ (s + t) = δ s * δ t) (w : InfinitePlace F) :
    IsRealLine σ J fun t => embArch σ J w (projArch σ J w (δ t)) := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter
    (fun t => GlobalTheory.Orb.archMat σ J τ (projArch σ J w (δ t)))
    ((GlobalTheory.Orb.continuous_archMat σ J τ).comp ((continuous_projArch σ J w).comp hc))
    (by simp only [h0, map_one]) (fun s t => by simp only [hm, map_mul])
  refine ⟨w, τ, Z, skew_of_exp_unitary _ _ fun t => ?_, fun t => ⟨_, rfl, hZ t⟩⟩
  rw [← hZ t, GlobalTheory.Orb.archMat_eq_archEquiv J hcm]
  exact (archEquiv J hcm τ _).2

end GlobalTheory.LineDerSum
