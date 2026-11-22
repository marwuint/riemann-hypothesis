import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementG
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundOfRestrictionOfProj
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.HighestVectorProjection
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.DerivativeKeepsSpaceHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.OmegaInjectiveHolds
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DischargeHeightBound
import Formalism.MahlerMeasure.FinalT
import Formalism.PolynomialDimension.MultinomialDepth.TieOps

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset

section Last

variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]

theorem resSatL_mono (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    {c c' : ℕ} (hc : c ≤ c') (h : ResSatL p LL J M ρ c) : ResSatL p LL J M ρ c' := by
  unfold ResSatL at h ⊢
  intro x hx hxI
  obtain ⟨g, hgY, hgI, hge⟩ := h x hx hxI
  refine ⟨((p : ℚ_[p]) ^ (c' - c)) • g, Submodule.smul_mem _ _ hgY, ?_, ?_⟩
  · have e : ((p : ℚ_[p]) ^ (c' - c)) • g = ((p : ℤ_[p]) ^ (c' - c)) • g := by
      rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ (c' - c)) g]
      simp
    rw [e]
    exact Submodule.smul_mem _ _ hgI
  · have hl : initPart (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ (c' - c)) • g)
        = ((p : ℚ_[p]) ^ (c' - c)) • initPart (Fin.last K, ρ) 0 g :=
      (resL p (Fin.last K, ρ) 0).map_smul _ g
    rw [hl, hge, smul_smul, ← pow_add, Nat.sub_add_cancel hc]

theorem resOntoK_of_resSatL (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (c0 : ℕ) (h : ResSatL p LL J M ρ c0) : ResOntoK p LL J M ρ := by
  classical
  unfold ResOntoK
  unfold ResSatL at h
  intro x hx
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ_[p])
    (x.support.image fun m => MvPolynomial.coeff m x)
  have hb' : ∀ m, ∃ y : ℤ_[p], algebraMap ℤ_[p] ℚ_[p] y = (b : ℤ_[p]) • MvPolynomial.coeff m x := by
    intro m
    by_cases hm : m ∈ x.support
    · obtain ⟨y, hy⟩ := hb _ (Finset.mem_image_of_mem _ hm)
      exact ⟨y, hy⟩
    · refine ⟨0, ?_⟩
      have h0 : MvPolynomial.coeff m x = 0 := by
        by_contra hne
        exact hm (MvPolynomial.mem_support_iff.2 hne)
      rw [h0, smul_zero, map_zero]
  choose y hy using hb'
  have hbx : algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]) • x ∈ IntPol p (Fin (K + 1) × Fin r) := by
    refine LinearMap.mem_range.2 ⟨∑ m ∈ x.support, monomial m (y m), ?_⟩
    change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) (∑ m ∈ x.support, monomial m (y m)) = _
    rw [map_sum]
    conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff x]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.map_monomial, hy m, MvPolynomial.smul_monomial]
    congr 1
  obtain ⟨g, hgY, hgI, hge⟩ := h _ (Submodule.smul_mem _ _ hx) hbx
  have hs0 : algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hp0 : ((p : ℚ_[p]) ^ c0) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  refine ⟨((p : ℚ_[p]) ^ c0 * algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]))⁻¹ • g, Submodule.smul_mem _ _ hgY, ?_⟩
  rw [initPart_smul, hge, smul_smul, smul_smul]
  have h1 : ((p : ℚ_[p]) ^ c0 * algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]))⁻¹ * (p : ℚ_[p]) ^ c0
      * algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]) = 1 := by
    field_simp
  rw [h1, one_smul]

theorem resMMZL (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e1 c0 : ℕ) (hHP : HypP p LL ρ e1) (hHE : HypE p LL ρ e1) (hSat : ResSatL p LL J M ρ c0)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ XH p LL J M ρ w)
    (hxI : x ∈ IntPol p (Fin (K + 1) × Fin r)) :
    ∃ h ∈ MMwZ p LL J M ρ w, initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ (e1 + c0)) • x := by
  obtain ⟨hx1, hxW⟩ := Submodule.mem_inf.mp hx
  obtain ⟨hxX, hxH⟩ := Submodule.mem_inf.mp hx1
  obtain ⟨h0, hh0, hh0I, hres⟩ := hSat x hxX hxI
  obtain ⟨PE, hPE, -, hInt⟩ := hypE_eproj LL ρ e1 hHE (K + 1) le_rfl w
  have hY := wtComp_Y LL J M w h0 hh0
  have hW := wtComp_mem (p := p) LL (K + 1) w h0
  refine ⟨((p : ℚ_[p]) ^ e1) • PE (wtComp p LL (K + 1) w h0), Submodule.mem_inf.mpr
    ⟨Submodule.smul_mem (MMw p LL J M ρ w) _ (eproj_Y LL J M ρ w e1 hHP PE hPE _ hY hW),
      hInt _ (Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hY).1, wtComp_int LL (K + 1) w h0 hh0I⟩) hW⟩, ?_⟩
  change resL p (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ e1) • PE (wtComp p LL (K + 1) w h0)) = _
  change resL p (Fin.last K, ρ) 0 h0 = _ at hres
  rw [map_smul, ← eproj_res LL (K + 1) ρ w PE hPE (Fin.last K) 0 _ hW, wtComp_res, hres,
    wtComp_fix LL (K + 1) w _ (Submodule.smul_mem _ _ hxW), map_smul,
    eproj_fix LL (K + 1) ρ w PE hPE x (Submodule.mem_inf.mpr ⟨hxH, hxW⟩), smul_smul, ← pow_add]

theorem satAtL (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e e1 c0 : ℕ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LLw.vec (Fin.last K) = true)
    (he : e ≤ LLw.deg (Fin.last K))
    (hP : HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hE : HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hS : ResSatL p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ c0) :
    SatAt p LLw J M ρ w e (e1 + c0) := by
  intro x hx hxI
  obtain ⟨y, hy, rfl⟩ :=
    (grSpan_eq LLw J M ρ w e e1 hr hρ hv he hP hE (resOntoK_of_resSatL _ J _ ρ c0 hS) x).mp hx
  rw [pow_mul_int_iff] at hxI
  obtain ⟨h, hh, hres⟩ := resMMZL (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ
    (shiftWt w ρ e) e1 c0 hP hE hS y hy hxI
  refine (graded_eq_holds p K r LLw J M ρ w e hv he _).mpr ⟨h, hh, ?_⟩
  rw [hres, mul_smul_comm]

theorem setLast_total_le (LL : Letters (K + 1)) (o : ℕ) (ho : o ≤ LL.deg (Fin.last K)) :
    (setLast LL o).total ≤ LL.total := by
  unfold Letters.total
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = Fin.last K
  · subst hi
    simpa [setLast] using ho
  · simp [setLast, Function.update_of_ne hi]

end Last

theorem graded_bound_saturation_holds : GradedBoundOfSaturation := by
  intro p _ K r _ LLw q J M ρ e1 c0 κ hr hρ hv hPE hS hκ w e k g hli hspan
  by_cases he : e ≤ LLw.deg (Fin.last K)
  · obtain ⟨hP, hE⟩ := hPE (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
    refine graded_piece_bound_holds p K r LLw J M ρ w e ((K + 3) * e1) (e1 + c0) κ
      (projAtOf_of highest_vector_projection p K r LLw J M ρ w e e1 hr hρ hv he hP hE (resOntoK_of_resSatL _ J _ ρ c0 (hS e he)))
      (satAtL LLw J M ρ w e e1 c0 hr hρ hv he hP hE (hS e he)) ?_ k g hli hspan
    have : (K + 3) * e1 + 2 * (e1 + c0) = (K + 5) * e1 + 2 * c0 := by ring
    rw [this]; exact hκ
  · rw [graded_bot_holds p K r LLw J M ρ w e (not_le.mp he)] at hspan
    have hk : k = 0 := by
      by_contra hk
      have h0 : g ⟨0, Nat.pos_of_ne_zero hk⟩ ∈ Submodule.span ℤ_[p] (Set.range g) :=
        Submodule.subset_span ⟨_, rfl⟩
      rw [hspan, Submodule.mem_bot] at h0
      exact hli.ne_zero _ h0
    subst hk
    simp

theorem kapC_mono (p n : ℕ) {d d' : ℕ} (h : d ≤ d') : kapC p n d ≤ kapC p n d' := by
  unfold kapC
  exact Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))

theorem hypPE_setLast {p : ℕ} [Fact p.Prime] {K r : ℕ} (LLw : Letters (K + 1)) (ρ : Fin r) :
    ∀ o ≤ LLw.deg (Fin.last K),
      HypP p (setLast LLw o) ρ (kapC p r LLw.total) ∧ HypE p (setLast LLw o) ρ (kapC p r LLw.total) :=
  fun o ho =>
    ⟨Formalism.InvariantFactorPaths.PW.Top.dischargeP p (K + 1) r (setLast LLw o) ρ _ (kapC_mono p r (setLast_total_le LLw o ho)),
      Formalism.InvariantFactorPaths.PW.Top.dischargeE p (K + 1) r (setLast LLw o) ρ _ (kapC_mono p r (setLast_total_le LLw o ho))⟩

section Ties

variable {N : ℕ}

theorem grid_le (T : TieData) (Yl n₀ dd : Fin T.t → ℕ) (n : Fin T.t → ℕ)
    (hn : n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))) :
    ∀ i, n i ≤ n₀ i + dd i * (Yl i - 1) := by
  intro i
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 (Fintype.mem_piFinset.1 hn i)
  rw [← hji]
  have hj' : j ≤ Yl i - 1 := by
    have := Finset.mem_range.1 hj
    omega
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hj') _

theorem takeD_vec_last (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (n : Fin T.t → ℕ) (i : Fin T.t) :
    ((LL.setTies T n).takeD (T.pos i + 1)).vec (Fin.last (T.pos i)) = true := by
  obtain ⟨h1, hv, -⟩ := hadm.2.1 i
  simp [Letters.takeD, Letters.setTies, show T.pos i < N by omega, hv]

end Ties

end Formalism.InvariantFactorPaths.L4
