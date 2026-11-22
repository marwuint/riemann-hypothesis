import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.CompactAbelianCharacters
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.NewformLiftCuspidality

open Ad3 Ad3.R

theorem fd_preimage (T : 𝔸[ℚ] ≃ₜ 𝔸[ℚ]) (σ : ℚ ≃ ℚ)
    (hT : ∀ (q : ℚ) x, T (algebraMap ℚ 𝔸[ℚ] q + x) = algebraMap ℚ 𝔸[ℚ] (σ q) + T x) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (T ⁻¹' fundamentalSet ℚ) (adeleMeasure ℚ) := by
  refine IsAddFundamentalDomain.mk'
    ((measurableSet_fundamentalSet ℚ).preimage T.continuous.measurable).nullMeasurableSet fun x => ?_
  obtain ⟨k, hk, hu⟩ := existsUnique_sub_mem_fundamentalSet ℚ (T x)
  refine ⟨⟨algebraMap ℚ 𝔸[ℚ] (σ.symm (-k)), _, rfl⟩, ?_, ?_⟩
  · change T (algebraMap ℚ 𝔸[ℚ] (σ.symm (-k)) + x) ∈ fundamentalSet ℚ
    rw [hT, σ.apply_symm_apply, map_neg, neg_add_eq_sub]
    exact hk
  · rintro ⟨_, ξ, rfl⟩ h
    have h' : T (algebraMap ℚ 𝔸[ℚ] ξ + x) ∈ fundamentalSet ℚ := h
    rw [hT] at h'
    have e : -σ ξ = k := hu _ (by
      show T x - algebraMap ℚ 𝔸[ℚ] (-σ ξ) ∈ fundamentalSet ℚ
      rw [map_neg, sub_neg_eq_add, add_comm]; exact h')
    refine Subtype.ext ?_
    change algebraMap ℚ 𝔸[ℚ] ξ = algebraMap ℚ 𝔸[ℚ] (σ.symm (-k))
    rw [← e, neg_neg, σ.symm_apply_apply]

theorem hT_symm (T : 𝔸[ℚ] ≃ₜ 𝔸[ℚ]) (σ : ℚ ≃ ℚ)
    (hT : ∀ (q : ℚ) x, T (algebraMap ℚ 𝔸[ℚ] q + x) = algebraMap ℚ 𝔸[ℚ] (σ q) + T x) (q : ℚ) (x : 𝔸[ℚ]) :
    T.symm (algebraMap ℚ 𝔸[ℚ] q + x) = algebraMap ℚ 𝔸[ℚ] (σ.symm q) + T.symm x := by
  apply T.injective
  rw [hT, T.apply_symm_apply, T.apply_symm_apply, σ.apply_symm_apply]

def scaleH (α : ℚˣ) : 𝔸[ℚ] ≃ₜ 𝔸[ℚ] := Homeomorph.smul (pri α)

def Cq : Type := Multiplicative (AdeleQuotient ℚ)

instance : CommGroup Cq := inferInstanceAs (CommGroup (Multiplicative (AdeleQuotient ℚ)))
instance : TopologicalSpace Cq := inferInstanceAs (TopologicalSpace (Multiplicative (AdeleQuotient ℚ)))
instance : IsTopologicalGroup Cq := inferInstanceAs (IsTopologicalGroup (Multiplicative (AdeleQuotient ℚ)))
instance : CompactSpace Cq := inferInstanceAs (CompactSpace (AdeleQuotient ℚ))
instance : T2Space Cq := inferInstanceAs (T2Space (AdeleQuotient ℚ))
instance : MeasurableSpace Cq := borel Cq
instance : BorelSpace Cq := ⟨rfl⟩

def pc (x : 𝔸[ℚ]) : Cq := Multiplicative.ofAdd (QuotientAddGroup.mk x : AdeleQuotient ℚ)

theorem isQuotientMap_pc : IsQuotientMap pc :=
  QuotientAddGroup.isQuotientMap_mk (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)

theorem continuous_pc : Continuous pc := isQuotientMap_pc.continuous

theorem pc_surjective : Function.Surjective pc := isQuotientMap_pc.surjective

theorem pc_add (x y : 𝔸[ℚ]) : pc (x + y) = pc x * pc y := rfl

theorem pc_zero : pc 0 = 1 := rfl

theorem pc_algebraMap_add (q : ℚ) (x : 𝔸[ℚ]) : pc (algebraMap ℚ 𝔸[ℚ] q + x) = pc x := by
  rw [pc_add]
  have : pc (algebraMap ℚ 𝔸[ℚ] q) = 1 :=
    congrArg Multiplicative.ofAdd ((QuotientAddGroup.eq_zero_iff _).2 ⟨q, rfl⟩)
  rw [this, one_mul]

def nu : Measure Cq := ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)).map pc

instance : IsProbabilityMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) :=
  ⟨by rw [Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]⟩

instance : IsProbabilityMeasure nu :=
  Measure.isProbabilityMeasure_map continuous_pc.aemeasurable

theorem addRight_add (a : 𝔸[ℚ]) (q : ℚ) (x : 𝔸[ℚ]) :
    Homeomorph.addRight a (algebraMap ℚ 𝔸[ℚ] q + x) = algebraMap ℚ 𝔸[ℚ] (Equiv.refl ℚ q) + Homeomorph.addRight a x := by
  simp [add_assoc]

instance : nu.IsMulLeftInvariant := by
  refine ⟨fun c => ?_⟩
  obtain ⟨a, rfl⟩ := pc_surjective c
  set T := Homeomorph.addRight a with hTdef
  have hTm : MeasurePreserving T (adeleMeasure ℚ) (adeleMeasure ℚ) := measurePreserving_add_right _ a
  have hD := measurableSet_fundamentalSet ℚ
  ext E hE
  have hEm : MeasurableSet (pc ⁻¹' E) := continuous_pc.measurable hE
  have hmul : Measurable (fun x : Cq => pc a * x) := (by fun_prop : Continuous fun x : Cq => pc a * x).measurable
  rw [Measure.map_apply hmul hE, nu, Measure.map_apply continuous_pc.measurable hE,
    Measure.map_apply continuous_pc.measurable (hmul hE),
    Measure.restrict_apply hEm, Measure.restrict_apply (continuous_pc.measurable (hmul hE))]
  have fd := fd_preimage T.symm (Equiv.refl ℚ).symm (hT_symm T (Equiv.refl ℚ) (addRight_add a))
  have h1 := fd.measure_set_eq (isAddFundamentalDomain_fundamentalSet ℚ) hEm (by
    rintro ⟨_, q, rfl⟩
    ext x
    change pc (algebraMap ℚ 𝔸[ℚ] q + x) ∈ E ↔ pc x ∈ E
    rw [pc_algebraMap_add])
  rw [← h1]
  have h2 : (pc ⁻¹' ((fun x => pc a * x) ⁻¹' E)) ∩ fundamentalSet ℚ =
      T ⁻¹' (pc ⁻¹' E ∩ T.symm ⁻¹' fundamentalSet ℚ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Homeomorph.symm_apply_apply]
    rw [hTdef, Homeomorph.coe_addRight, pc_add, mul_comm]
  rw [h2]
  exact hTm.measure_preimage (hEm.inter ((hD.preimage T.symm.continuous.measurable))).nullMeasurableSet

instance : nu.IsHaarMeasure := by
  haveI : nu.IsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_compact Set.univ isCompact_univ (by simp)
  exact {}

end GlobalTheory.CompanionTheory.NewformLiftCuspidality
end
