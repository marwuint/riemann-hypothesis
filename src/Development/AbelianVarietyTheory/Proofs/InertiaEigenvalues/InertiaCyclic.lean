import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff

noncomputable section
namespace GlobalTheory.TameInertiaCyclic
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_pow_norm (K : FinExt l) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ K.1, x ≠ 0 → ∃ a : ℤ, ‖x‖ ^ d = (l : ℝ) ^ a := by
  haveI := K.2
  refine ⟨Module.finrank ℚ_[l] ↥K.1, Module.finrank_pos, fun x hxK hx => ?_⟩
  have e := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (PadicAlgCl l) x
  rw [PadicAlgCl.spectralNorm_eq] at e
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[l] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have hn := minpoly.natDegree_pos hi
  have hd : (minpoly ℚ_[l] x).natDegree ∣ Module.finrank ℚ_[l] ↥K.1 := by
    have := minpoly.degree_dvd (K := ℚ_[l]) (x := (⟨x, hxK⟩ : ↥K.1)) (Algebra.IsIntegral.isIntegral _)
    rwa [IntermediateField.minpoly_eq] at this
  obtain ⟨c, hc⟩ := hd
  refine ⟨-((minpoly ℚ_[l] x).coeff 0).valuation * c, ?_⟩
  rw [hc, pow_mul, e, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hn.ne',
    Padic.norm_eq_zpow_neg_valuation h0, zpow_mul, zpow_natCast]

theorem exists_gen (K : FinExt l) :
    ∃ π ∈ K.1, π ≠ 0 ∧ ∀ x ∈ K.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π ^ k‖ := by
  obtain ⟨d, hd, H⟩ := exists_pow_norm K
  have hl0 : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  let S : AddSubgroup ℤ :=
    { carrier := {n | ∃ x ∈ K.1, x ≠ 0 ∧ ‖x‖ ^ d = (l : ℝ) ^ n}
      add_mem' := by
        rintro a b ⟨x, hx, hx0, ex⟩ ⟨y, hy, hy0, ey⟩
        exact ⟨x * y, mul_mem hx hy, mul_ne_zero hx0 hy0, by
          rw [norm_mul, mul_pow, ex, ey, zpow_add₀ hl0]⟩
      zero_mem' := ⟨1, one_mem _, one_ne_zero, by simp⟩
      neg_mem' := by
        rintro a ⟨x, hx, hx0, ex⟩
        exact ⟨x⁻¹, inv_mem hx, inv_ne_zero hx0, by rw [norm_inv, inv_pow, ex, zpow_neg]⟩ }
  obtain ⟨f, hf⟩ := Int.subgroup_cyclic S
  have hfS : f ∈ S := by rw [hf]; exact AddSubgroup.subset_closure rfl
  obtain ⟨π, hπ, hπ0, eπ⟩ := hfS
  refine ⟨π, hπ, hπ0, fun x hx hx0 => ?_⟩
  obtain ⟨a, ha⟩ := H x hx hx0
  have haS : a ∈ S := ⟨x, hx, hx0, ha⟩
  rw [hf, AddSubgroup.mem_closure_singleton] at haS
  obtain ⟨k, rfl⟩ := haS
  refine ⟨k, (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd.ne').1 ?_⟩
  rw [ha, norm_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, eπ, ← zpow_mul,
    smul_eq_mul, mul_comm]

theorem fix_of_near (K : FinExt l) (g : GQ l) (hst : ∀ x ∈ K.1, g x ∈ K.1)
    (hnear : ∀ x ∈ K.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) {N : ℕ} (hN : ¬ l ∣ N)
    (hgN : ∀ x ∈ K.1, (g ^ N) x = x) (y : Om l) (hy : y ∈ K.1) : g y = y := by
  by_contra hne
  have hx0 : g y - y ≠ 0 := sub_ne_zero.2 hne
  have hxK : g y - y ∈ K.1 := sub_mem (hst y hy) hy
  set x := g y - y with hx
  have h1 : ∀ i : ℕ, ‖(g ^ i) x - x‖ < ‖x‖ := by
    intro i
    induction i with
    | zero => simpa using hx0
    | succ i ih =>
      have e : (g ^ (i + 1)) x - x = (g ^ i) (g x - x) + ((g ^ i) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, map_sub (g ^ i)]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rw [norm_gal]; exact hnear x hxK hx0
  have h2 : ∀ k : ℕ, ‖((g ^ k) y - y) - (k : Om l) * x‖ < ‖x‖ := by
    intro k
    induction k with
    | zero => simpa using hx0
    | succ k ih =>
      have e : ((g ^ (k + 1)) y - y) - ((k + 1 : ℕ) : Om l) * x =
          (((g ^ k) y - y) - (k : Om l) * x) + ((g ^ k) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, hx, map_sub]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (h1 k))
  have hmn : ‖(N : Om l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hN)
  have := h2 N
  rw [hgN y hy, sub_self, zero_sub, norm_neg, norm_mul, hmn, one_mul] at this
  exact lt_irrefl _ this

def ratio (g : GQ l) (x : Om l) : OO l :=
  ⟨g x / x, by
    show ‖g x / x‖ ≤ 1
    rw [norm_div, norm_gal]; exact div_self_le_one _⟩

theorem ratio_mul (g : GQ l) (x y : Om l) : ratio g (x * y) = ratio g x * ratio g y :=
  Subtype.ext (by
    show g (x * y) / (x * y) = g x / x * (g y / y)
    rw [map_mul, mul_div_mul_comm])

theorem res_ratio_iff (g : GQ l) {x : Om l} (hx : x ≠ 0) :
    res (ratio g x) = 1 ↔ ‖g x - x‖ < ‖x‖ := by
  rw [← map_one (res (l := l)), res_eq_iff]
  show ‖g x / x - 1‖ < 1 ↔ _
  have : g x / x - 1 = (g x - x) / x := by field_simp
  rw [this, norm_div, div_lt_one (norm_pos_iff.2 hx)]

theorem res_ratio_zpow (g : GQ l) {x : Om l} (hx : x ≠ 0) (h : res (ratio g x) = 1) (k : ℤ) :
    res (ratio g (x ^ k)) = 1 := by
  induction k using Int.induction_on with
  | zero => rw [res_ratio_iff g (by simp)]; simp
  | succ k ih => rw [zpow_add_one₀ hx, ratio_mul, map_mul, ih, h, one_mul]
  | pred k ih =>
    have e : x ^ (-(k : ℤ)) = x ^ (-(k : ℤ) - 1) * x := by
      rw [← zpow_add_one₀ hx, sub_add_cancel]
    rwa [e, ratio_mul, map_mul, h, mul_one] at ih

theorem map_mem_Kur (g : GQ l) {c : Om l} (hc : c ∈ MaximalUnramifiedExtension l) : g c ∈ MaximalUnramifiedExtension l := by
  unfold MaximalUnramifiedExtension at hc
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hlm, hx⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  | algebraMap x => rw [g.commutes]; exact (MaximalUnramifiedExtension l).algebraMap_mem x
  | add x y _ _ hx hy => rw [map_add]; exact (MaximalUnramifiedExtension l).add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact (MaximalUnramifiedExtension l).inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact (MaximalUnramifiedExtension l).mul_mem hx hy

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

end GlobalTheory.TameInertiaCyclic
