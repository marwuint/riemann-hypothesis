import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} [hp : Fact p.Prime]

theorem finrank_eq_of_semilinear_surjective {W k M V : Type} [CommRing W] [Nontrivial W] [Field k]
    [AddCommGroup M] [Module W M] [Module.Free W M] [Module.Finite W M] [AddCommGroup V] [Module k V]
    {σ : W →+* k} (hσ : Function.Surjective σ) {q : ℕ} (hq : (q : k) = 0) (r : M →ₛₗ[σ] V)
    (hr : Function.Surjective r) (hk : ∀ m, r m = 0 → ∃ n, m = q • n) :
    Module.Finite k V ∧ Module.finrank k V = Module.finrank W M := by
  let b := Module.finBasis W M
  have h1 : LinearIndependent k fun i => r (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    choose w hw using fun i => hσ (c i)
    obtain ⟨n, hn⟩ := hk (∑ i, w i • b i) (by simpa only [map_sum, map_smulₛₗ, hw] using hc)
    have e := congrArg (fun m => σ (b.repr m i)) hn
    simpa [hq, hw, Finsupp.single_apply] using e
  have h2 : ⊤ ≤ Submodule.span k (Set.range fun i => r (b i)) := fun v _ => by
    obtain ⟨m, rfl⟩ := hr v
    rw [← b.sum_repr m, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨.of_basis (.mk h1 h2), by rw [Module.finrank_eq_card_basis (.mk h1 h2), Fintype.card_fin]⟩

variable (hW : Published.BarsottiTateDieudonne.WittModule) {K : Type} [Field K] (h : (p : K) = 0)
include hW h

omit hW in

theorem range_rigExtMap_relFrob (G : PDivGroup p K) :
    LinearMap.range (rigExtMap (relFrob h G)) = Submodule.span K (Set.range (absFrob h G).rig) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨x, rfl⟩
    have key : ∀ (P : (frobTwist h G).RigExt → Prop), P 0 → (∀ (r : K) y, P (r • (frobProj h G).rig y)) →
        (∀ x y, P x → P y → P (x + y)) → P x := fun P h0 h1 h2 => by
      letI := (frobRing h).toAlgebra
      obtain ⟨y, rfl⟩ := (liftSemi_rig_bijective (R := K) K G h
        (.inl (@Module.Flat.of_free K K _ _ (_) (@Module.Free.of_divisionRing K K _ _ (_))))).2 x
      induction y with
      | zero => exact (congrArg P (map_zero _)).mpr h0
      | add x y hx hy => exact (congrArg P (map_add _ _ _)).mpr (h2 _ _ hx hy)
      | tmul r y => exact h1 r y
    refine key (fun x => rigExtMap (relFrob h G) x ∈ Submodule.span K (Set.range (absFrob h G).rig))
      (by simp only [map_zero, zero_mem]) (fun r y => ?_) fun x y hx hy => ?_
    · rw [map_smul, rigExtMap_relFrob_rig]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
    · rw [map_add]
      exact add_mem hx hy
  · rintro _ ⟨y, rfl⟩
    exact ⟨_, rigExtMap_relFrob_rig h G y⟩

end PDivGroup

end GlobalTheory
