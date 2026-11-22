import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PerpLatticeTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalLatticeDecomposition

namespace ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
  ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def eps' (p : ℕ) {n : ℕ} (k : Fin n) : ℂ := if (k : ℕ) < p then 1 else -1

def uc (X : Data E r) (z0 : Frame X.Ψ r) (ξ : Fin r → E) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ :=
  v - (X.Hf z0 τ v (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
    Data.emb τ.1 ξ

section Uc

variable (X : Data E r) {z0 : Frame X.Ψ r} (ξ : Fin r → E) (τ : X.Ψ)

lemma uc_comb (hz : z0 ∈ X.dom) {n : ℕ} (a : Fin n → ℂ) (V : Fin n → Fin r → ℂ) :
    uc X z0 ξ τ (∑ k, a k • V k) = ∑ k, a k • uc X z0 ξ τ (V k) := by
  let L : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := X.ppos z0 τ, map_add' := X.ppos_add z0 τ,
      map_smul' := fun k u => X.ppos_smul_eq z0 τ k u }
  have hHf : ∀ u w, X.Hf z0 τ u w = hermC τ.1 X.Gm ((2 : ℂ) • L u - u) w := fun u w => rfl
  have hsum : X.Hf z0 τ (∑ k, a k • V k) (Data.emb τ.1 ξ) =
      ∑ k, a k * X.Hf z0 τ (V k) (Data.emb τ.1 ξ) := by
    rw [hHf, map_sum]
    simp only [map_smul]
    have e : (2 : ℂ) • ∑ k, a k • L (V k) - ∑ k, a k • V k =
        ∑ k, a k • ((2 : ℂ) • L (V k) - V k) := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_sub, smul_comm]
    rw [e, hermC_sum_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hermC_smul_left, hHf]
  unfold uc
  rw [hsum]
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_smul, smul_smul,
    mul_div_assoc]

lemma uc_perp (hξξ : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (v v' : Fin r → ℂ)
    (hv : hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0) (hv' : hermC τ.1 X.Gm v' (Data.emb τ.1 ξ) = 0) :
    hermC τ.1 X.Gm (uc X z0 ξ τ v') (uc X z0 ξ τ v) = hermC τ.1 X.Gm v' v := by
  have hsubR : ∀ u w w' : Fin r → ℂ,
      hermC τ.1 X.Gm u (w - w') = hermC τ.1 X.Gm u w - hermC τ.1 X.Gm u w' := by
    intro u w w'
    simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
  have hsmulR : ∀ (c : ℂ) (u w : Fin r → ℂ),
      hermC τ.1 X.Gm u (c • w) = conj c * hermC τ.1 X.Gm u w := by
    intro c u w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hsym : hermC τ.1 X.Gm (Data.emb τ.1 ξ) v = 0 := by
    have hc : hermC τ.1 X.Gm (Data.emb τ.1 ξ) v = conj (hermC τ.1 X.Gm v (Data.emb τ.1 ξ)) := by
      simp only [hermC, map_sum, map_mul, Complex.conj_conj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← ReciprocityTheory.ChartRestriction.G.FD.emb_cc, X.Gm_herm]
      ring
    rw [hc, hv, map_zero]
  unfold uc
  simp only [hermC_sub_left, hsubR, hermC_smul_left, hsmulR, hv', hξξ, hsym, mul_zero, sub_zero]

end Uc

end

end ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination
