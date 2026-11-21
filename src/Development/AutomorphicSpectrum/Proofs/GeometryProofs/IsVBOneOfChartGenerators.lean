import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {E : Type} [AddCommGroup E] [Module Ω E]

section Units

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem unitAt.zpow {u : Ω} (hu : unitAt ξ p u) (n : ℤ) : unitAt ξ p (u ^ n) := by
  obtain ⟨h0, h1, h2⟩ := hu
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · refine ⟨zpow_ne_zero _ h0, ?_, ?_⟩
    · rw [zpow_natCast]; exact pow_mem h1 n
    · rw [zpow_natCast, ← inv_pow]; exact pow_mem h2 n
  · refine ⟨zpow_ne_zero _ h0, ?_, ?_⟩
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem h2 n
    · rw [zpow_neg, zpow_natCast, inv_inv]; exact pow_mem h1 n

theorem unitAt.prod {K : Type} (s : Finset K) {u : K → Ω} (hu : ∀ k ∈ s, unitAt ξ p (u k)) :
    unitAt ξ p (∏ k ∈ s, u k) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun k hk => (hu k hk).1, prod_mem fun k hk => (hu k hk).2.1, ?_⟩
  rw [← Finset.prod_inv_distrib]
  exact prod_mem fun k hk => (hu k hk).2.2

theorem span_singleton_eq_of_unitAt {u : Ω} (hu : unitAt ξ p u) {e e' : E} (h : e' = u • e) :
    Submodule.span (regAt ξ p) {e'} = Submodule.span (regAt ξ p) {e} := by
  obtain ⟨h0, h1, h2⟩ := hu
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨u, h1⟩, h.symm⟩
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨⟨u⁻¹, h2⟩, ?_⟩
    show u⁻¹ • e' = e
    rw [h, smul_smul, inv_mul_cancel₀ h0, one_smul]

end Units

namespace Lat

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem mem_dual {L : Lat ξ E} {p : Cpt ξ} {w : Module.Dual Ω E} :
    w ∈ L.dual p ↔ ∀ e ∈ L p, w e ∈ regAt ξ p := Iff.rfl

theorem IsFrameAt.dual {L : Lat ξ E} {r : ℕ} (b : Module.Basis (Fin r) Ω E) {p : Cpt ξ}
    (h : L.IsFrameAt b p) : L.dual.IsFrameAt b.dualBasis p := by
  refine ⟨b.dualBasis.linearIndependent, le_antisymm ?_ ?_⟩
  · intro w hw
    have hb : ∀ i, w (b i) ∈ regAt ξ p := fun i =>
      mem_dual.1 hw (b i) (by rw [h.2]; exact Submodule.subset_span ⟨i, rfl⟩)
    have hsum : w = ∑ i, w (b i) • b.dualBasis i := by
      simpa [Module.Basis.coe_dualBasis] using (b.sum_dual_apply_smul_coord w).symm
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ (⟨w (b i), hb i⟩ : regAt ξ p)
      (Submodule.subset_span ⟨i, rfl⟩ : b.dualBasis i ∈ Submodule.span (regAt ξ p) (Set.range b.dualBasis))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine mem_dual.2 fun e he => ?_
    rw [h.2] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [Module.Basis.dualBasis_apply_self]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => simpa using zero_mem _
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      have : (b.dualBasis i) (a • x) = (a : Ω) * (b.dualBasis i) x := by
        rw [show a • x = (a : Ω) • x from rfl, map_smul, smul_eq_mul]
      rw [this]
      exact mul_mem a.2 hx

end Lat

section Pull

variable {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}

theorem Dominates.map_genPt (h : Dominates ξ' ξ f i) : f (genPt ξ') = genPt ξ := by
  let pt' : Spec (CommRingCat.of Ω') := IsLocalRing.closedPoint Ω'
  let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
  have h1 : (ξ' ≫ f) pt' = (Spec.map (CommRingCat.ofHom i) ≫ ξ) pt' :=
    congrArg (fun g : Spec (CommRingCat.of Ω') ⟶ X => g pt') h
  have h2 : (Spec.map (CommRingCat.ofHom i)) pt' = pt :=
    (inferInstance : Subsingleton (PrimeSpectrum Ω)).elim _ _
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h2] at h1
  exact h1

theorem Dominates.specializes (h : Dominates ξ' ξ f i) (p' : Cpt ξ') : genPt ξ ⤳ f p'.1 := by
  rw [← h.map_genPt]
  exact p'.2.map f.continuous

theorem Lat.pull_apply {F : Type} [AddCommGroup F] [Module Ω' F] (L : Lat ξ E) (h : Dominates ξ' ξ f i)
    (j : E →+ F) (p' : Cpt ξ') :
    L.pull ξ' f j p' = Submodule.span (regAt ξ' p') (j '' (L ⟨f p'.1, h.specializes p'⟩ : Set E)) := by
  show Submodule.span _ _ = _
  congr 1
  ext e'
  constructor
  · rintro ⟨_, e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨h.specializes p', e, he, rfl⟩

end Pull

namespace Lat

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

section Multi

variable {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω}

theorem block_ratio_mem {p : Cpt ξ} {c : (k : K) → ι k}
    (h : InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) (i : ι k) :
    y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h2 := h.2 (Function.update c k i)
  have e1 : ∏ k', y ⟨k', c k'⟩ = y ⟨k, c k⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ :=
    (Finset.mul_prod_erase _ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)).symm
  have e2 : ∏ k', y ⟨k', Function.update c k i k'⟩ = y ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ := by
    rw [← Finset.mul_prod_erase _ (fun k' => y ⟨k', Function.update c k i k'⟩) (Finset.mem_univ k)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun k' hk' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
  have hP : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0 := by
    intro h0
    exact h.1 (by show ∏ k', y ⟨k', c k'⟩ = 0; rw [e1, h0, mul_zero])
  simp only [e1, e2] at h2
  rwa [mul_div_mul_right _ _ hP] at h2

theorem block_coord_ne_zero {p : Cpt ξ} {c : (k : K) → ι k}
    (h : InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) : y ⟨k, c k⟩ ≠ 0 :=
  Finset.prod_ne_zero_iff.1 h.1 k (Finset.mem_univ k)

end Multi

end Lat

end GlobalTheory.CompanionTheory.Ar
