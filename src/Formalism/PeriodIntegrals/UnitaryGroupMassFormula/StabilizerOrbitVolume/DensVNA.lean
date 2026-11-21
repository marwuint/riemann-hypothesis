import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVCos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.PosNear

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct

private theorem exists_pow_smul_mem_nhds_of_isCompact' {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : Set V) (hLc : IsCompact L)
    (π : 𝕜) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) (N : Set V) (hN : N ∈ 𝓝 (0 : V)) :
    ∃ k : ℕ, ∀ y ∈ L, π ^ k • y ∈ N := by
  have h : ∀ᶠ c in 𝓝 (0 : 𝕜), ∀ y ∈ L, c • y ∈ N := by
    refine hLc.eventually_forall_of_forall_eventually fun y _ => ?_
    have ht : Tendsto (fun z : 𝕜 × V => z.1 • z.2) (𝓝 ((0 : 𝕜), y)) (𝓝 ((0 : 𝕜) • y)) :=
      continuous_smul.continuousAt
    rw [zero_smul] at ht
    exact ht hN
  exact (hπ.eventually h).exists

theorem hasCOSub_of_lat {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : HasCOSub V := by
  intro N hN
  obtain ⟨k, hk⟩ := exists_pow_smul_mem_nhds_of_isCompact' (L : Set V) hLc π hπ N hN
  have hc : π ^ k ≠ 0 := pow_ne_zero k h0
  have himg : ((L.map (DistribMulAction.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) =
      (fun x => π ^ k • x) '' (L : Set V) := by
    ext x
    simp
  refine ⟨L.map (DistribMulAction.toAddMonoidHom V (π ^ k)), ?_, ?_, ?_⟩
  · rw [himg]
    exact isOpenMap_smul₀ hc _ hLo
  · rw [himg]
    exact hLc.image (continuous_const_smul _)
  · rw [himg]
    rintro _ ⟨y, hy, rfl⟩
    exact hk y hy

theorem exists_pow_tendsto_zero_Fv {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  refine ⟨π, fun h => ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have h1 : Valued.v (π : v.adicCompletion F) < 1 := by
      rw [hv]
      decide
    have hlt : ‖(π : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt

def latSub {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) :
    AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E) where
  carrier := latV (M := M) (n := a) b v
  add_mem' := by
    intro x y hx hy
    simp only [latV, Set.mem_setOf_eq] at hx hy ⊢
    intro i j k
    simp only [Pi.add_apply, map_add, Finsupp.add_apply]
    exact add_mem (hx i j k) (hy i j k)
  zero_mem' := by
    simp only [latV, Set.mem_setOf_eq]
    intro i j k
    simp only [Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx
    simp only [latV, Set.mem_setOf_eq] at hx ⊢
    intro i j k
    simp only [Pi.neg_apply, map_neg, Finsupp.neg_apply]
    exact neg_mem (hx i j k)

def scaledB (𝕜 : Type) {V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (L : AddSubgroup V)
    (Λ : AddSubgroup V) : Prop :=
  ∃ c : 𝕜, c ≠ 0 ∧ Λ = L.map (DistribMulAction.toAddMonoidHom V c)

theorem isCOBasis_scaled {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : IsCOBasis (scaledB 𝕜 L) := by
  intro N hN
  obtain ⟨k, hk⟩ := exists_pow_smul_mem_nhds_of_isCompact' (L : Set V) hLc π hπ N hN
  have hc : π ^ k ≠ 0 := pow_ne_zero k h0
  have himg : ((L.map (DistribMulAction.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) =
      (fun x => π ^ k • x) '' (L : Set V) := by
    ext x
    simp
  refine ⟨L.map (DistribMulAction.toAddMonoidHom V (π ^ k)), ⟨π ^ k, hc, rfl⟩, ?_, ?_, ?_⟩
  · rw [himg]
    exact isOpenMap_smul₀ hc _ hLo
  · rw [himg]
    exact hLc.image (continuous_const_smul _)
  · rw [himg]
    rintro _ ⟨y, hy, rfl⟩
    exact hk y hy

theorem isCOBasis_latSub {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) :
    IsCOBasis (scaledB (Fv F v) (latSub b v a M)) := by
  obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
  exact isCOBasis_scaled (latSub b v a M)
    (PositiveNearLattice.isClopen_latV (b := b) (v := v) a M).isOpen
    (PositiveNearLattice.isCompact_latV (b := b) (v := v) a M) π h0 hπ

end PI.VolStabSW
