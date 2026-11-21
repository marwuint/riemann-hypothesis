import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.CardToMultisetEqDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.EqZeroOfVecMulTmat

namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def ptx (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) : Fin d → C :=
  Matrix.vecMul (G.lc p ga n - ∑ s : Fin n, ∑ b,
    (ptx G p γ ga s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)) (tmat γ)⁻¹
termination_by n
decreasing_by exact s.isLt

def ptw (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) : Fin d → C :=
  G.lc p ga n - ∑ s ∈ Finset.range n, ∑ b,
    (ptx G p γ ga s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)

theorem ptx_eq (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) :
    ptx G p γ ga n = Matrix.vecMul (ptw G p γ ga n) (tmat γ)⁻¹ := by
  rw [ptx, ptw, Finset.sum_range]

private theorem lgCurve_zero' (G : LogFGL v d) (a : Fin d) :
    G.lgCurve (fun _ => (0 : PowerSeries C)) a = 0 := by
  have h0 : HasSubst (fun _ : Fin d => (0 : PowerSeries C)) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun _ => by simp)
  ext j
  rw [map_zero]
  change MvPowerSeries.coeff (Finsupp.single () j) (subst _ (G.lg a)) = 0
  rw [MvPowerSeries.coeff_subst h0]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e = 0
  · subst he
    rw [coeff_zero_eq_constantCoeff_apply, G.lg_const a, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact he (Finsupp.ext hcon)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [hs]),
      map_zero, smul_zero]

private theorem lc_at_zero_eq_tangent (G : LogFGL v d) (p : ℕ) (ga : Fin d → PowerSeries C)
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) : G.lc p ga 0 = tangent ga := by
  funext a
  have hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - (fun _ => (0 : PowerSeries C)) b := by
    intro b
    show (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - 0
    rw [pow_one, sub_zero]
    exact PowerSeries.X_dvd_iff.mpr (h0 b)
  have h1 := lgCurve_sub_dvd (β := fun _ => (0 : PowerSeries C)) G h0 (fun _ => by simp) 1 hk a
  simp only [lgCurve_zero', sub_zero] at h1
  have h2 := PowerSeries.X_pow_dvd_iff.mp h1 1 (by norm_num)
  rw [map_sub, sub_eq_zero] at h2
  show PowerSeries.coeff (p ^ 0) (G.lgCurve ga a) = PowerSeries.coeff 1 (ga a)
  rw [pow_zero, h2]

theorem ptx_rel (G : LogFGL v d) (p : ℕ) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hdet : v (tmat γ).det = 0) (ga : Fin d → PowerSeries C)
    (n : ℕ) :
    G.lc p ga n = ∑ s ∈ Finset.range (n + 1), ∑ b,
      (ptx G p γ ga s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s) := by
  have hlast : ∑ b, (ptx G p γ ga n b) ^ (p ^ (n - n)) • G.lc p (γ b) (n - n) =
      ptw G p γ ga n := by
    simp only [Nat.sub_self, pow_zero, pow_one]
    rw [Finset.sum_congr rfl (fun b _ => by rw [lc_at_zero_eq_tangent G p (γ b) (fun c => (hγ b c).1)]),
      sum_smul_tangent, ptx_eq, vecMul_inv_tmat hdet]
  rw [Finset.sum_range_succ, hlast, ptw]
  abel

def pcurve (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C) (x : ℕ → Fin d → C) :
    ℕ → Fin d → PowerSeries C
  | 0 => 0
  | s + 1 => G.add (pcurve G p γ x s) (G.sumF fun b => expC (p ^ s) (rescaleCurve (x s b) (γ b)))

theorem isCurve_pcurve (G : LogFGL v d) {p : ℕ} (hp : p ≠ 0) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) :
    ∀ n, (∀ s < n, ∀ b, IsIntV v (x s b)) → IsCurve v (pcurve G p γ x n)
  | 0, _ => isCurve_zero
  | n + 1, hx => isCurve_add G (isCurve_pcurve G hp hγ x n fun s hs b => hx s (by omega) b)
      (isCurve_sumF G _ fun b => isCurve_expC (pow_ne_zero _ hp)
        (isCurve_rescale (hx n (by omega) b) (hγ b)))

theorem lgCurve_pcurve (G : LogFGL v d) {p : ℕ} (hp : p ≠ 0) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) :
    ∀ n, (∀ s < n, ∀ b, IsIntV v (x s b)) → ∀ a, G.lgCurve (pcurve G p γ x n) a =
      ∑ s ∈ Finset.range n, ∑ b, PowerSeries.expand (p ^ s) (pow_ne_zero _ hp)
        (PowerSeries.rescale (x s b) (G.lgCurve (γ b) a))
  | 0, _, a => by simp [pcurve, lgCurve_zero]
  | n + 1, hx, a => by
      have hx' : ∀ s < n, ∀ b, IsIntV v (x s b) := fun s hs b => hx s (by omega) b
      have hc : ∀ b, IsCurve v (expC (p ^ n) (rescaleCurve (x n b) (γ b))) := fun b =>
        isCurve_expC (pow_ne_zero _ hp) (isCurve_rescale (hx n (by omega) b) (hγ b))
      rw [pcurve, lgCurve_add G (fun b => (isCurve_pcurve G hp hγ x n hx' b).1)
        (fun b => (isCurve_sumF G _ hc b).1), lgCurve_pcurve G hp hγ x n hx' a,
        lgCurve_sumF G _ hc, Finset.sum_range_succ]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [lgCurve_expC G (pow_ne_zero _ hp) (fun c => (isCurve_rescale (hx n (by omega) b) (hγ b) c).1),
        lgCurve_rescale G _ (fun c => (hγ b c).1)]

end

end ReciprocityTheory.ChartRestriction.G.Sh.PTb
