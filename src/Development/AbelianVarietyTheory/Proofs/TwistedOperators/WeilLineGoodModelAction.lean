import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfTensEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSmulSemi

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM Filter Topology
open scoped SchwartzMap GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical

noncomputable section

namespace GlobalTheory.ArchJointCont

theorem continuous_of_weak {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)) (h : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, Continuous fun f => T (A f)) : Continuous A := by
  haveI : BarrelledSpace ℂ 𝓢(V, ℂ) := GlobalTheory.schwartzMap_barrelledSpace V
  refine (schwartz_withSeminorms ℂ V ℂ).continuous_of_continuous_comp A fun i => ?_
  set p : Seminorm ℂ 𝓢(V, ℂ) := schwartzSeminormFamily ℂ V ℂ i
  have hp : Continuous p := (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i
  let j₀ : 𝓢(V, ℂ) →ₗ[ℂ] GlobalTheory.DiffDecay.WithSemi p := LinearMap.id
  have hj : Continuous j₀ := by
    refine continuous_of_continuousAt_zero j₀ ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    have := hp.tendsto 0
    rw [map_zero] at this
    exact this
  let j : 𝓢(V, ℂ) →L[ℂ] GlobalTheory.DiffDecay.WithSemi p := ⟨j₀, hj⟩
  have hnorm : ∀ x, ‖j x‖ = p x := fun x => rfl
  refine Seminorm.continuous_of_lowerSemicontinuous _ fun f₀ y hy => ?_
  change y < p (A f₀) at hy
  rcases lt_or_ge y 0 with hy0 | hy0
  · exact Eventually.of_forall fun f => lt_of_lt_of_le hy0 (apply_nonneg _ _)
  have hex : ∃ L : StrongDual ℂ (GlobalTheory.DiffDecay.WithSemi p), y * ‖L‖ < ‖L (j (A f₀))‖ := by
    by_contra hne
    push_neg at hne
    have h1 : ‖NormedSpace.inclusionInDoubleDual ℂ (GlobalTheory.DiffDecay.WithSemi p) (j (A f₀))‖ ≤ y :=
      ContinuousLinearMap.opNorm_le_bound _ hy0 fun L => by
        rw [NormedSpace.dual_def]; exact hne L
    rw [show NormedSpace.inclusionInDoubleDual ℂ (GlobalTheory.DiffDecay.WithSemi p) (j (A f₀)) =
      NormedSpace.inclusionInDoubleDualLi ℂ (j (A f₀)) from rfl, LinearIsometry.norm_map, hnorm] at h1
    exact absurd hy (not_lt.2 h1)
  obtain ⟨L, hL⟩ := hex
  have hc : Continuous fun f => ‖L (j (A f))‖ := (h (L.comp j)).norm
  filter_upwards [(hc.tendsto f₀).eventually_const_lt hL] with f hf
  change y < p (A f)
  have h2 : ‖L (j (A f))‖ ≤ ‖L‖ * p (A f) := by rw [← hnorm]; exact L.le_opNorm _
  have h4 : y * ‖L‖ < ‖L‖ * p (A f) := lt_of_lt_of_le hf h2
  by_contra hcon
  push_neg at hcon
  nlinarith [norm_nonneg L]

theorem exists_adm (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (T : SInf F κ →L[ℂ] ℂ) :
    ∃ l ∈ (adeleClass F).adm κ, ∀ (f : SInf F κ) (g : (κ → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) → ℂ),
      l (pureA F ⇑f g) = g 0 * T f := by
  let lift : (κ → mixedEmbedding.mixedSpace F) → (κ → AF F) := fun y i =>
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0)
  let sl : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) := LinearMap.funLeft ℂ ℂ lift
  let co : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hco : Function.Injective co := DFunLike.coe_injective
  let e := LinearEquiv.ofInjective co hco
  obtain ⟨T₂, hT₂⟩ := LinearMap.exists_extend (T.toLinearMap ∘ₗ e.symm.toLinearMap)
  have hT₂f : ∀ f : SInf F κ, T₂ ⇑f = T f := fun f => by
    have := congrArg (fun m => m (e f)) hT₂
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe] at this
    rw [LinearEquiv.ofInjective_apply] at this
    exact this
  have hsl : ∀ (f : SInf F κ) g, sl (pureA F ⇑f g) = g 0 • ⇑f := fun f g => by
    funext y
    show pureA F ⇑f g (lift y) = g 0 * f y
    simp only [pureA, lift, RingEquiv.apply_symm_apply]
    rw [mul_comm]
    rfl
  refine ⟨T₂ ∘ₗ sl, fun g _ => ⟨g 0 • T, fun f => ?_⟩, fun f g => ?_⟩
  · simp [hsl, hT₂f]
  · simp [hsl, hT₂f]

end GlobalTheory.ArchJointCont
