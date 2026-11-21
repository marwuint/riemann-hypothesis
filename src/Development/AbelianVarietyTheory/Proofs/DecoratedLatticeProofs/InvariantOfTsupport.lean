import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing

noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology

namespace GlobalTheory.LocMod.Inhab

section Abstract

variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {N : Submodule ℂ (G → ℂ)} {K : AddSubgroup G}

theorem ind_mem (h : IsBichar χ) (hN : ∀ y, ∀ Φ ∈ N, (fun t => χ t y * Φ t) ∈ N)
    (hsep : ∀ u, u ∉ K → ∃ y, (∀ κ ∈ K, χ κ y = 1) ∧ χ u y ≠ 1) (R : Finset G) :
    ∀ Φ ∈ N, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → Φ 0 ≠ 0 → (∀ t, Φ t ≠ 0 → t ∈ K ∨ ∃ r ∈ R, t - r ∈ K) → ind K ∈ N := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Φ hΦ h1 h2 h3
    convert N.smul_mem (Φ 0)⁻¹ hΦ using 1
    funext t
    by_cases ht : t ∈ K
    · have := h1 t ht 0
      rw [zero_add] at this
      simp [ind, ht, this, h2]
    · have : Φ t = 0 := by_contra fun hh => by simpa [ht] using h3 t hh
      simp [ind, ht, this]
  | insert r R _ ih =>
    intro Φ hΦ h1 h2 h3
    by_cases hr : r ∈ K
    · refine ih Φ hΦ h1 h2 fun t ht => ?_
      rcases h3 t ht with hh | ⟨s, hs, hh⟩
      · exact Or.inl hh
      · rcases Finset.mem_insert.1 hs with rfl | hs
        · exact Or.inl (by simpa using add_mem hh hr)
        · exact Or.inr ⟨s, hs, hh⟩
    · obtain ⟨y, hy, hne⟩ := hsep r hr
      refine ih _ (N.sub_mem (hN y Φ hΦ) (N.smul_mem (χ r y) hΦ)) (fun u hu t => ?_) ?_ fun t ht => ?_
      · simp only [Pi.sub_apply, Pi.smul_apply, h.left, hy u hu, h1 u hu, mul_one]
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h.zero_left, ← sub_mul]
        exact mul_ne_zero (sub_ne_zero.2 hne.symm) h2
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← sub_mul] at ht
        rcases h3 t (right_ne_zero_of_mul ht) with hh | ⟨s, hs, hh⟩
        · exact Or.inl hh
        · rcases Finset.mem_insert.1 hs with rfl | hs
          · refine absurd ?_ (left_ne_zero_of_mul ht)
            rw [← add_sub_cancel s t, h.left, hy _ hh, mul_one, sub_self]
          · exact Or.inr ⟨s, hs, hh⟩

theorem mem_of_ind_mem (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hK : ind K ∈ N) (R : Finset G) :
    ∀ Φ : G → ℂ, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → (∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ K) → Φ ∈ N := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Φ _ h3
    convert N.zero_mem using 1
    funext t
    by_contra ht
    simpa using h3 t ht
  | insert s R _ ih =>
    intro Φ h2 h3
    have hm := N.smul_mem (Φ s) (hN (-s) _ hK)
    have hval : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ≠ 0 → Φ t ≠ 0 ∧ t + -s ∉ K := by
      intro t ht
      have hn : t + -s ∉ K := fun hh => ht (by
        have := h2 _ hh s
        rw [show s + (t + -s) = t by abel] at this
        simp [ind, hh, this])
      exact ⟨by simpa [ind, hn] using ht, hn⟩
    have := ih (Φ - Φ s • fun t => ind K (t + -s)) (fun u hu t => by
      simp only [Pi.sub_apply, Pi.smul_apply, h2 u hu]
      rw [add_right_comm, ind_add K _ hu]) fun t ht => by
        obtain ⟨s', hs', hu⟩ := h3 t (hval t ht).1
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · exact absurd (by rwa [← sub_eq_add_neg]) (hval _ ht).2
        · exact ⟨s', hs', hu⟩
    simpa using add_mem this hm

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem eventually_invariant {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) :
    ∀ᶠ u in 𝓝 (0 : Matrix Y Y' k), ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t :=
  hΦ.2.isCompact.eventually_forall_of_forall_eventually (P := fun u t => Φ (t + u) = Φ t) fun x _ => by
    have h1 := ((continuous_snd.add continuous_fst).tendsto' ((0 : Matrix Y Y' k), x) x (add_zero x)).eventually
      (hΦ.1.eventually_eq x)
    have h2 := (continuous_snd.tendsto ((0 : Matrix Y Y' k), x)).eventually (hΦ.1.eventually_eq x)
    filter_upwards [h1, h2] with z a b using a.trans b.symm

theorem invariant_of_tsupport {Φ : Matrix Y Y' k → ℂ} {K : AddSubgroup (Matrix Y Y' k)}
    (h : ∀ u ∈ K, ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t) (u : Matrix Y Y' k) (hu : u ∈ K) (t : Matrix Y Y' k) :
    Φ (t + u) = Φ t := by
  by_cases ht : t ∈ tsupport Φ
  · exact h u hu t ht
  by_cases ht' : t + u ∈ tsupport Φ
  · rw [← h _ (neg_mem hu) _ ht', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport ht, image_eq_zero_of_notMem_tsupport ht']

theorem exists_cosets {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (a : kˣ) :
    ∃ R : Finset (Matrix Y Y' k), ∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ box Y Y' a := by
  obtain ⟨R, -, hR⟩ := hΦ.2.isCompact.elim_nhds_subcover (fun r => {t | t - r ∈ box Y Y' a}) fun r _ =>
    ((isOpen_box a).preimage (continuous_sub_right r)).mem_nhds (by simp)
  exact ⟨R, fun t ht => by simpa using hR (subset_tsupport Φ ht)⟩

theorem sb_le {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {N : Submodule ℂ (Matrix Y Y' k → ℂ)}
    (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hN' : ∀ y, ∀ Φ ∈ N, (fun t => pairing ψ t y * Φ t) ∈ N)
    {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (h0 : Φ ≠ 0) (hΦN : Φ ∈ N) : SB (Matrix Y Y' k) ≤ N := by
  classical
  intro Ψ hΨ
  obtain ⟨a, ha⟩ := exists_box_subset ((eventually_invariant hΦ).and (eventually_invariant hΨ))
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  obtain ⟨R, hR⟩ := exists_cosets hΦ a
  obtain ⟨R', hR'⟩ := exists_cosets hΨ a
  refine mem_of_ind_mem hN (ind_mem (isBichar_pairing ψ) hN'
    (fun u hu => let ⟨y, hy, hne⟩ := exists_sep hd a hu; ⟨y, fun κ hκ => pairing_box hd hκ hy, hne⟩)
    (R.image (· - x)) _ (hN x Φ hΦN) (fun u hu t => ?_) (by rwa [zero_add]) fun t ht => ?_) R' Ψ
    (invariant_of_tsupport fun u hu => (ha u hu).2) hR'
  · rw [add_right_comm]
    exact invariant_of_tsupport (fun u hu => (ha u hu).1) u hu _
  · obtain ⟨r, hr, h⟩ := hR _ ht
    exact Or.inr ⟨_, Finset.mem_image_of_mem _ hr, by convert h using 1; abel⟩

end GlobalTheory.LocMod.Inhab
end
