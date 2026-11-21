import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.ChiExtend

theorem placesOver_finite' (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem maximalIdeal_le_comap {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) {O₀ O₁ : Type}
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra ℤ_[p] O₀] [Module.Finite ℤ_[p] O₀]
    [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra ℤ_[q] O₁] [Module.Finite ℤ_[q] O₁]
    (φ : O₀ →+* O₁) (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z') :
    IsLocalRing.maximalIdeal O₀ ≤ Ideal.comap φ (IsLocalRing.maximalIdeal O₁) := by
  subst h
  have hc : φ.comp (algebraMap ℤ_[p] O₀) = algebraMap ℤ_[p] O₁ := by
    ext z
    exact hφ z z HEq.rfl
  haveI : (Ideal.comap φ (IsLocalRing.maximalIdeal O₁)).IsPrime := Ideal.comap_isPrime _ _
  have h1 : (Ideal.comap (algebraMap ℤ_[p] O₀) (Ideal.comap φ (IsLocalRing.maximalIdeal O₁))).IsMaximal := by
    rw [Ideal.comap_comap, hc]
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  have h2 := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h1
  rw [IsLocalRing.eq_maximalIdeal h2]

theorem continuous_of_le_comap {O₀ O₁ : Type} [CommRing O₀] [IsLocalRing O₀] [TopologicalSpace O₀]
    [IsTopologicalRing O₀] [CommRing O₁] [IsLocalRing O₁] [TopologicalSpace O₁] [IsTopologicalRing O₁]
    (h₀ : IsAdic (IsLocalRing.maximalIdeal O₀)) (h₁ : IsAdic (IsLocalRing.maximalIdeal O₁))
    (φ : O₀ →+* O₁) (hφ : IsLocalRing.maximalIdeal O₀ ≤ Ideal.comap φ (IsLocalRing.maximalIdeal O₁)) :
    Continuous φ := by
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := (isAdic_iff.1 h₁).2 s hs
  have ho := (isAdic_iff.1 h₀).1 n
  refine Filter.mem_map.2 <| Filter.mem_of_superset (ho.mem_nhds (Ideal.zero_mem _)) fun x hx => hn ?_
  exact (Ideal.pow_right_mono hφ n |>.trans (Ideal.le_comap_pow φ n)) hx

theorem cyc_heq (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q)
    (σ : G F Ω) : HEq ((cycZ F Ω p σ : ℤ_[p]ˣ) : ℤ_[p]) ((cycZ F Ω q σ : ℤ_[q]ˣ) : ℤ_[q]) := by
  subst h
  rfl

end GlobalTheory.ChiExtend

namespace GlobalTheory.ChiExtend

theorem iotaO_injective {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) :
    Function.Injective (iotaO N A i) := by
  show Function.Injective (((A.iotaQC i).toRingHom.comp (A.iotaQ i)).comp (algebraMap (N.O i) (FractionRing (N.O i))))
  simp only [RingHom.coe_comp]
  exact (A.iotaQC i).injective.comp ((A.iotaQ i).injective.comp (IsFractionRing.injective _ _))

theorem eq_of_dense {X O : Type*} [TopologicalSpace X] [CommRing O] [IsLocalRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (h : IsAdic (IsLocalRing.maximalIdeal O)) (hH : IsHausdorff (IsLocalRing.maximalIdeal O) O)
    {f g : X → O} (hf : Continuous f) (hg : Continuous g) {s : Set X} (hs : Dense s) (he : ∀ x ∈ s, f x = g x) :
    f = g := by
  funext x
  rw [← sub_eq_zero]
  apply hH.haus' (f x - g x)
  intro n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  have hcl : IsClosed ((fun y => f y - g y) ⁻¹' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O)) := by
    refine IsClosed.preimage (hf.sub hg) ?_
    exact AddSubgroup.isClosed_of_isOpen (IsLocalRing.maximalIdeal O ^ n).toAddSubgroup
      ((isAdic_iff.1 h).1 n)
  have hsub : s ⊆ (fun y => f y - g y) ⁻¹' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := by
    intro y hy
    simp only [Set.mem_preimage, he y hy, sub_self, SetLike.mem_coe]
    exact Ideal.zero_mem _
  have := closure_minimal hsub hcl
  rw [hs.closure_eq] at this
  exact this (Set.mem_univ x)

end GlobalTheory.ChiExtend

