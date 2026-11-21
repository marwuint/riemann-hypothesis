import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def projProj : (((k : Unit) → projBlocks K i k) → ℂ) →ₗ[ℂ] (Fin i → ℂ) where
  toFun s := ∑ σ : K →+* ℂ, embComp σ (fun q => s fun _ => q)
  map_add' s s' := by
    funext j
    simp only [Finset.sum_apply, Pi.add_apply, embComp, mul_add, Finset.sum_add_distrib]
  map_smul' c s := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, embComp, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun m _ => by ring

theorem projProj_apply (s : ((k : Unit) → projBlocks K i k) → ℂ) :
    projProj s = ∑ σ : K →+* ℂ, embComp σ (fun q => s fun _ => q) := rfl

end

end GroundTheory.Heights₂.Heights
