import Mathlib
import GroundTheory.AutomorphicForms.KernelTrace
import GroundTheory.AutomorphicForms.TraceFormulaConvolution

open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

section Algebra

variable {G : Type*} [Group G]

def centralizerIn (Γ : Subgroup G) (γ : G) : Subgroup G :=
  Γ ⊓ Subgroup.centralizer {γ}

theorem centralizerIn_le (Γ : Subgroup G) (γ : G) : centralizerIn Γ γ ≤ Γ :=
  inf_le_left

theorem mem_centralizer_singleton_iff {γ δ : G} :
    δ ∈ Subgroup.centralizer {γ} ↔ δ⁻¹ * γ * δ = γ := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    rw [mul_assoc, h, inv_mul_cancel_left]
  · intro h
    calc γ * δ = δ * (δ⁻¹ * γ * δ) := by group
      _ = δ * γ := by rw [h]

def conjOrbitFun {E : Type*} (H : Subgroup G) {γ : G} (hH : H ≤ Subgroup.centralizer {γ})
    (f : G → E) : RightCosetSpace H → E :=
  Quotient.lift (fun x => f (x⁻¹ * γ * x)) (by
    rintro a b ⟨η, rfl⟩
    have h : (η : G)⁻¹ * γ * η = γ := mem_centralizer_singleton_iff.1 (hH η.2)
    change f (((η : G) * b)⁻¹ * γ * ((η : G) * b)) = f (b⁻¹ * γ * b)
    congr 1
    calc ((η : G) * b)⁻¹ * γ * ((η : G) * b) = b⁻¹ * ((η : G)⁻¹ * γ * η) * b := by group
      _ = b⁻¹ * γ * b := by rw [h])

@[simp] theorem conjOrbitFun_mk {E : Type*} (H : Subgroup G) {γ : G}
    (hH : H ≤ Subgroup.centralizer {γ}) (f : G → E) (x : G) :
    conjOrbitFun H hH f (mk H x) = f (x⁻¹ * γ * x) :=
  rfl

end Algebra

section Geometric

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

instance discreteTopology_centralizerIn (γ : G) : DiscreteTopology (centralizerIn Γ γ) :=
  DiscreteTopology.of_continuous_injective
    (f := Subgroup.inclusion (centralizerIn_le Γ γ))
    (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

omit [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [μ.IsMulRightInvariant] in

theorem setIntegral_smul_set {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : G)
    (s : Set G) (F : G → E) : ∫ x in a • s, F x ∂μ = ∫ x in s, F (a * x) ∂μ := by
  have h := (measurePreserving_mul_left μ a).setIntegral_preimage_emb
    (MeasurableEquiv.mulLeft a).measurableEmbedding F (a • s)
  have hpre : (fun x => a * x) ⁻¹' (a • s) = s := by
    ext x
    simp [Set.mem_smul_set_iff_inv_smul_mem]
  rw [hpre] at h
  exact h.symm

variable [CompactSpace (RightCosetSpace Γ)]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] in
theorem mem_smul_set_iff' (a y : G) (s : Set G) : y ∈ a • s ↔ a⁻¹ * y ∈ s := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]

omit [LocallyCompactSpace G] [T2Space G] [CompactSpace (RightCosetSpace Γ)] in
theorem eq_of_mul_mem_fundamentalDomain {η₁ η₂ : Γ} {y : G}
    (h₁ : (η₁ : G) * y ∈ fundamentalDomain Γ) (h₂ : (η₂ : G) * y ∈ fundamentalDomain Γ) :
    η₁ = η₂ :=
  (existsUnique_smul_mem_fundamentalDomain Γ y).unique h₁ h₂

end Geometric

end RightCosetSpace

end

end GroundTheory.Automorphic
