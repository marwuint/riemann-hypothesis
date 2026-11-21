import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement

open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp

noncomputable section
namespace GlobalTheory.KernelComm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}

section Indicator
variable [Fintype n'] (q : Unif k) {P₁ : Pair k n'} {e₁ : n' → k} (he : P₁.HasVal e₁ 1) (Q : Pair k n)
  (x : Matrix n n' k)
include he

open Classical in

theorem sum_target :
    ∑ Q₁ ∈ withKer Q.lat with cross q Q₁ Q = 1, phiOne P₁ Q₁ x = midInd q P₁.ker e₁ Q x := by
  have hm : ∀ Q₁ : Pair k n, Maps P₁ Q₁ x ↔ (∀ y ∈ P₁.ker, x *ᵥ y ∈ Q₁.ker) ∧ Q₁.HasVal (x *ᵥ e₁) 1 := fun Q₁ => by
    rw [maps_iff_glue he Q₁.hasVal_vec, Pair.hasVal_one_iff Q₁.hasVal_vec]
  rw [midInd, mulVec_smul]
  split_ifs with h
  · have hg : IsGlue Q.lat (x *ᵥ e₁) := (isGlue_iff q).2 ⟨Q.isLat, fun h0 =>
      one_ne_zero (h.2.unique (Pair.mem_ker.1 (Pair.smul_mem_ker q.mem_max h0))), h.2.mem⟩
    rw [Finset.sum_eq_single_of_mem (glue hg)]
    · exact if_pos ((hm _).2 ⟨by rw [glue_ker]; exact h.1, glue_hasVal hg⟩)
    · exact Finset.mem_filter.2 ⟨mem_withKer.2 (glue_ker hg),
        (cross_hasVal q (glue_ker hg).symm (glue_hasVal hg)).unique h.2⟩
    · exact fun Q₁ h1 h2 => if_neg fun h3 =>
        h2 ((eq_glue_iff hg).2 ⟨mem_withKer.1 (Finset.mem_filter.1 h1).1, ((hm _).1 h3).2⟩)
  · refine Finset.sum_eq_zero fun Q₁ h1 => if_neg fun h3 => h ?_
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h1
    rw [mem_withKer] at h1
    exact ⟨h1 ▸ ((hm _).1 h3).1, h2 ▸ cross_hasVal q h1.symm ((hm _).1 h3).2⟩

open Classical in

theorem sum_source :
    midInd q P₁.ker e₁ Q x = ∑ P ∈ withLat P₁.ker with cross q P₁ P = 1, phiOne P Q x := by
  rw [midInd]
  have hq : q.1 • e₁ ∈ P₁.ker := Pair.smul_mem_ker q.mem_max he.mem
  split_ifs with h
  · let f : P₁.ker →ₗ[𝒪[k]] 𝓀[k] := Q.fn ∘ₗ ((Matrix.mulVecLin x).restrictScalars 𝒪[k]).restrict h.1
    have hf : ∀ y : P₁.ker, Q.HasVal (x *ᵥ y) (f y) := fun y => ⟨h.1 y y.2, rfl⟩
    have h1 : f ⟨_, hq⟩ = 1 := (hf ⟨_, hq⟩).unique h.2
    let R : Pair k n' := ⟨P₁.ker, P₁.ker_isLat, f, fun h0 => by simp [h0] at h1⟩
    have hR : Maps R Q x := ⟨h.1, fun _ => rfl⟩
    rw [Finset.sum_eq_single_of_mem R]
    · exact (if_pos hR).symm
    · exact Finset.mem_filter.2 ⟨mem_withLat.2 rfl, (cross_hasVal q (P := R) rfl he).unique ⟨hq, h1⟩⟩
    · refine fun P hP h2 => if_neg fun h3 => h2 (Pair.ext fun y a => ?_)
      have hl : P.lat = R.lat := mem_withLat.1 (Finset.mem_filter.1 hP).1
      rw [maps_iff_hasVal] at hR h3
      constructor
      · intro hy
        have h4 := R.hasVal_fn ⟨y, hl ▸ hy.mem⟩
        exact (hR _ _ h4).unique (h3 _ _ hy) ▸ h4
      · intro hy
        have h4 := P.hasVal_fn ⟨y, hl ▸ hy.mem⟩
        exact (h3 _ _ h4).unique (hR _ _ hy) ▸ h4
  · refine (Finset.sum_eq_zero fun P h1 => if_neg fun h3 => h ?_).symm
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h1
    rw [mem_withLat] at h1
    exact ⟨h1 ▸ h3.1, maps_iff_hasVal.1 h3 _ _ (h2 ▸ cross_hasVal q h1 he)⟩

end Indicator

theorem card_withKer (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    (withKer L).card = (withLat L).card := by
  classical
  letI := Fintype.ofFinite (Red L)
  letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))
  have hc : Fintype.card (Red L) = Fintype.card (Module.Dual 𝓀[k] (Red L)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := 𝓀[k]),
      Module.natCard_eq_pow_finrank (K := 𝓀[k]) (V := Module.Dual 𝓀[k] (Red L)), Subspace.dual_finrank_eq]
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, sum_withKer L q, sum_withLat L]
  simp [hc]

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem exists_det (q : Unif k) (P : Pair k n) :
    ∃ d : GL n k, d • P.ker = P.lat ∧ Matrix.GeneralLinearGroup.det d = q.unit⁻¹ := by
  obtain ⟨i⟩ : Nonempty n := by
    by_contra h
    haveI := not_nonempty_iff.1 h
    exact P.fn_ne (LinearMap.ext fun y => by rw [Subsingleton.elim y 0]; simp)
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq (GL n k) (stdPair k i) P
  have hdet : (Matrix.diagonal (Function.update (1 : n → k) i (q.1 : k))).det = (q.1 : k) := by
    simp [Matrix.det_diagonal, Finset.prod_update_of_mem]
  let d : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ q.ne_zero)
  have hd : ∀ (y : n → k) j, (d • y) j = Function.update (1 : n → k) i (q.1 : k) j * y j := fun y j =>
    Matrix.mulVec_diagonal _ _ _
  have h1 : d⁻¹ • (stdPair k i).ker = (stdPair k i).lat := by
    ext y
    rw [mem_smul_iff, inv_inv, Pair.mem_ker, stdPair_hasVal]
    change _ ↔ y ∈ stdLat k n
    rw [mem_stdLat]
    constructor
    · rintro ⟨h, h0⟩ j
      by_cases hj : j = i
      · subst hj
        obtain ⟨s, hs⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff _).1 h0)
        have h2 : (q.1 : k) * y j = q.1 * s := by simpa [hd] using congrArg Subtype.val hs
        rw [mul_left_cancel₀ q.ne_zero h2]
        exact s.2
      · simpa [hd, hj] using h j
    · intro h
      refine ⟨fun j => ?_, (residue_eq_zero_iff _).2 (q.mem_max_iff.2 ⟨⟨y i, h i⟩, Subtype.ext (by simp [hd])⟩)⟩
      by_cases hj : j = i
      · subst hj
        simpa [hd] using mul_mem q.1.2 (h j)
      · simpa [hd, hj] using h j
  refine ⟨a * d⁻¹ * a⁻¹, by rw [Pair.smul_ker, Pair.smul_lat, mul_smul, mul_smul, inv_smul_smul, h1], ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm, _root_.inv_inj]
  exact Units.ext hdet

theorem valuation_det (q : Unif k) (P : Pair k n) {g : GL n k} (hg : g • P.ker = P.lat) :
    valuation k ((Matrix.GeneralLinearGroup.det g * q.unit : kˣ) : k) = 1 := by
  obtain ⟨d, hd, hdet⟩ := exists_det q P
  have := valuation_det_of_fix P.ker (h := d⁻¹ * g) (by rw [mul_smul, hg, ← hd, inv_smul_smul])
  rwa [map_mul, map_inv, hdet, inv_inv, mul_comm] at this

variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
  {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
  (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)

def KK : Form k n' V' →ₗ[ℂ] Form k n V :=
  (EqForm π).subtype ∘ₗ (evalEquiv π Q₀).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (θ.flip (phiOneSB P₀ Q₀) ∘ₗ LinearMap.proj P₀) fun φ => theta_mem hμ hθ P₀ Q₀ (φ P₀)

theorem K_eq (φ : EqForm π') : (K hμ hθ P₀ Q₀ φ).1 = KK hμ hθ P₀ Q₀ φ.1 := rfl

theorem eq_of_base {φ φ' : Form k n V} (h : φ ∈ EqForm π) (h' : φ' ∈ EqForm π) (e : φ Q₀ = φ' Q₀) : φ = φ' := by
  ext Q
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [h g, h' g, e]

end GlobalTheory.KernelComm
