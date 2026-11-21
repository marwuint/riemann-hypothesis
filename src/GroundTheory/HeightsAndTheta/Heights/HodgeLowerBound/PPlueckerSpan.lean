import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenericMinors

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace PlueckerSpan

theorem sum_prod_mul_det_indicator {R : Type} [CommRing R] {s N : ℕ} (M : Matrix (Fin s) (Fin N) R)
    (t : Fin s → Fin N) :
    ∑ c : Fin s → Fin N, (∏ a, M a (c a)) *
        (Matrix.of fun a j => if c a = t j then (1 : R) else 0).det =
      (Matrix.of fun a j => M a (t j)).det := by
  classical
  have hrow : (Matrix.of fun a j => M a (t j)) =
      fun a => ∑ b, M a b • fun j => if b = t j then (1 : R) else 0 := by
    ext a j
    simp [Finset.sum_apply]
  rw [hrow]
  change _ = Matrix.detRowAlternating _
  have h1 := (Matrix.detRowAlternating (R := R) (n := Fin s)).toMultilinearMap.map_sum
    (fun a b => M a b • fun j => if b = t j then (1 : R) else 0)
  simp only [AlternatingMap.coe_multilinearMap] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h2 := (Matrix.detRowAlternating (R := R) (n := Fin s)).toMultilinearMap.map_smul_univ
    (fun a => M a (c a)) (fun a j => if c a = t j then (1 : R) else 0)
  simp only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at h2
  rw [h2]
  rfl

theorem sum_prod_mul_apply_eq {Ω R E : Type} [Field Ω] [CommRing R] [Algebra Ω R] [AddCommGroup E] [Module Ω E]
    {s N : ℕ} (e : Module.Basis (Fin N) Ω E) (M : Matrix (Fin s) (Fin N) R)
    (φ : Module.Dual Ω (⋀[Ω]^s E)) :
    ∑ c : Fin s → Fin N, (∏ a, M a (c a)) * algebraMap Ω R (φ (exteriorPower.ιMulti Ω s (e ∘ c))) =
      ∑ T : Set.powersetCard (Fin N) s, algebraMap Ω R (φ (e.exteriorPower s T)) *
        (Matrix.of fun a j => M a (Set.powersetCard.ofFinEmbEquiv.symm T j)).det := by
  classical
  have hc : ∀ c : Fin s → Fin N, algebraMap Ω R (φ (exteriorPower.ιMulti Ω s (e ∘ c))) =
      ∑ T : Set.powersetCard (Fin N) s, algebraMap Ω R (φ (e.exteriorPower s T)) *
        (Matrix.of fun a j => if c a = Set.powersetCard.ofFinEmbEquiv.symm T j then (1 : R) else 0).det := by
    intro c
    conv_lhs => rw [← (e.exteriorPower s).sum_repr (exteriorPower.ιMulti Ω s (e ∘ c))]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [map_smul, smul_eq_mul, map_mul, mul_comm, exteriorPower.basis_repr_apply,
      exteriorPower.ιMultiDual_apply_ιMulti, RingHom.map_det]
    congr 2
    ext a j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Function.comp_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  simp_rw [hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← sum_prod_mul_det_indicator M, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem span_eq_top_of_dual {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {s N M : ℕ}
    (b : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω (⋀[Ω]^s E))
    (h : ∀ A : Fin s → Fin N, StrictMono A → ∃ a : Fin M → Ω, ∀ A' : Fin s → Fin N, StrictMono A' →
      ∑ m, a m * φ m (exteriorPower.ιMulti Ω s (b ∘ A')) = if A' = A then 1 else 0) :
    Submodule.span Ω (Set.range φ) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.2 fun ψ => ?_
  rw [← (b.exteriorPower s).sum_dual_apply_smul_coord ψ]
  refine Submodule.sum_mem _ fun T _ => Submodule.smul_mem _ _ ?_
  obtain ⟨a, ha⟩ := h _ (Set.powersetCard.ofFinEmbEquiv.symm T).strictMono
  have hT : (b.exteriorPower s).coord T = ∑ m, a m • φ m := by
    refine (b.exteriorPower s).ext fun T' => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    rw [ha _ (Set.powersetCard.ofFinEmbEquiv.symm T').strictMono, Finsupp.single_apply]
    have hiff : ((Set.powersetCard.ofFinEmbEquiv.symm T' : Fin s → Fin N) =
        Set.powersetCard.ofFinEmbEquiv.symm T) ↔ T' = T := by
      constructor
      · intro h'
        exact Set.powersetCard.ofFinEmbEquiv.symm.injective (DFunLike.coe_injective h')
      · rintro rfl
        rfl
    by_cases hTT : T' = T
    · rw [if_pos hTT, if_pos (hiff.2 hTT)]
    · rw [if_neg hTT, if_neg (fun h' => hTT (hiff.1 h'))]
  rw [hT]
  exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

end PlueckerSpan

end GroundTheory.Heights₂.Heights.LowerBoundFree
