import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormProdSignMulDetSubmatrixSubOneLe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsContinuousGramSchmidt
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul

open NumberField ReciprocityTheory.ChartRestriction.G.FD Topology

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace CuspNet

theorem exists_finset_rmul_near_one {r : ℕ} (X : Data E r) {K : Set (Frame X.Ψ r)}
    (hK : IsCompact K) (hKd : K ⊆ X.dom) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : Finset (Frame X.Ψ r), (∀ y ∈ N, y ∈ K) ∧ ∀ x ∈ K, ∃ A : Frame X.Ψ r,
      (∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ δ) ∧ rmul x A ∈ N := by
  obtain ⟨N, hN, hcov⟩ := hK.elim_nhdsWithin_subcover
    (fun y => {x | ∀ τ a b, ‖((mat x τ)⁻¹ * mat y τ) a b - (if a = b then 1 else 0)‖ ≤ δ})
    (fun y hy => by
      simp only [Set.ofPred_forall]
      refine Filter.iInter_mem.2 fun τ => Filter.iInter_mem.2 fun a =>
        Filter.iInter_mem.2 fun b => ?_
      have hc : ContinuousOn (fun x : Frame X.Ψ r =>
          ‖((mat x τ)⁻¹ * mat y τ) a b - (if a = b then 1 else 0)‖) K := by
        refine (ContinuousOn.sub ?_ continuousOn_const).norm
        simp only [Matrix.mul_apply]
        refine continuousOn_finsetSum _ fun k _ => ContinuousOn.mul ?_ continuousOn_const
        exact GramSchmidtCont.continuousOn_inv_apply (GramSchmidtCont.continuous_mat X τ)
          (fun x hx => (hKd hx τ).1) a k
      have h0 : ‖((mat y τ)⁻¹ * mat y τ) a b - (if a = b then 1 else 0)‖ < δ := by
        rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hKd hy τ).1), Matrix.one_apply,
          sub_self, norm_zero]
        exact hδ
      exact (hc y hy).eventually (eventually_le_nhds h0))
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
  refine ⟨fun τ => ((mat x τ)⁻¹ * mat y τ : Matrix (Fin r) (Fin r) ℂ), hxy, ?_⟩
  convert hy using 1
  funext τ
  show mat x τ * ((mat x τ)⁻¹ * mat y τ) = mat y τ
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hKd hx τ).1)]

end CuspNet

namespace CuspNet

end CuspNet

end GlobalTheory
