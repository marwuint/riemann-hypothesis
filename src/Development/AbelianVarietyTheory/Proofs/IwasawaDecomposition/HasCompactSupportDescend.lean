import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientInvariantMeasureExistsUniqueUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarIsMulRightInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open MeasureTheory Topology
open scoped Pointwise

namespace GlobalTheory.LocLanglands.InvInt

section General

variable {G : Type} [Group G] (H : Subgroup G)

def descend : (G → ℂ) →ₗ[ℂ] (G ⧸ H → ℂ) where
  toFun f q := f (q.out)⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {H}

theorem descend_mk {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (g : G) :
    descend H f (g : G ⧸ H) = f g⁻¹ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  show f ((g : G ⧸ H).out)⁻¹ = _
  rw [hh, mul_inv_rev]
  exact hf _ (H.inv_mem h.2) _

theorem descend_mul_right {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (x : G) :
    descend H (fun g => f (g * x)) = fun q => descend H f (x⁻¹ • q) := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descend_mk (fun u hu g => by rw [mul_assoc, hf u hu]), MulAction.Quotient.smul_mk, descend_mk hf]
  simp

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_descend {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (hc : Continuous f) :
    Continuous (descend H f) := by
  refine (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr ?_
  have : descend H f ∘ QuotientGroup.mk = fun g => f g⁻¹ := funext (descend_mk hf)
  rw [this]
  exact hc.comp continuous_inv

theorem hasCompactSupport_descend [T2Space (G ⧸ H)] {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g)
    {C : Set G} (hC : IsCompact C) (hs : ∀ g, f g ≠ 0 → ∃ u ∈ H, ∃ c ∈ C, g = u * c) :
    HasCompactSupport (descend H f) := by
  refine HasCompactSupport.intro (hC.inv.image QuotientGroup.continuous_mk) fun q hq => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descend_mk hf]
  by_contra h
  obtain ⟨u, hu, c, hc, e⟩ := hs _ h
  refine hq ⟨c⁻¹, by simpa using hc, QuotientGroup.eq.2 ?_⟩
  have : g = c⁻¹ * u⁻¹ := by rw [← mul_inv_rev, ← e, inv_inv]
  rw [this]
  simpa using hu

end General

open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem isClosed_unipB : IsClosed (unipB k (Fin m) : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : ∀ i j, Continuous fun g : GL (Fin m) k => g.val i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have : (unipB k (Fin m) : Set (GL (Fin m) k)) =
      (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin m) k | g.val i j = 0}) ∩ ⋂ i, {g : GL (Fin m) k | g.val i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_eq (hc _ _) continuous_const).inter (isClosed_iInter fun _ => isClosed_eq (hc _ _) continuous_const)

end GlobalTheory.LocLanglands.InvInt
