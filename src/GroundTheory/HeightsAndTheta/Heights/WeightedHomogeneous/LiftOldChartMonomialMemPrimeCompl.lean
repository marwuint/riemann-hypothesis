import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SectionCycle

section Local

variable {S : Type*} [CommRing S]

theorem length_localized_eq {J J₁ W : Ideal S} [W.IsPrime] (hJ : J ≤ J₁) {t : S} (ht : t ∉ W)
    (hmul : ∀ x ∈ J₁, t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J₁)) := by
  let q : (S ⧸ J) →ₗ[S] (S ⧸ J₁) := Submodule.mapQ J J₁ LinearMap.id hJ
  let φ := IsLocalizedModule.map W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl (S ⧸ J))
    (LocalizedModule.mkLinearMap W.primeCompl (S ⧸ J₁)) q
  have hφ : ∀ (x : S) (s : W.primeCompl), φ (LocalizedModule.mk (Submodule.Quotient.mk x) s) =
      LocalizedModule.mk (Submodule.Quotient.mk x) s := by
    intro x s
    rw [IsLocalizedModule.map_LocalizedModules]
    rfl
  have htW : t ∈ W.primeCompl := ht
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y
    refine LocalizedModule.induction_on (fun m s hy ↦ ?_) y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J m
    rw [hφ, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hy
    obtain ⟨u, hu⟩ := hy
    simp only [smul_zero, one_smul] at hu
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul] at hu
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
    refine ⟨⟨t, htW⟩ * u, ?_⟩
    simp only [smul_zero, one_smul]
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul, Submonoid.coe_mul, mul_assoc]
    exact hmul _ hu
  have hsurj : Function.Surjective φ := by
    intro y
    refine LocalizedModule.induction_on (fun m s ↦ ?_) y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J₁ m
    exact ⟨LocalizedModule.mk (Submodule.Quotient.mk x) s, hφ x s⟩
  exact ((LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq

theorem mem_minimalPrimes_iff {J J₁ W : Ideal S} (hJ : J ≤ J₁) {t : S} (ht : t ∉ W)
    (hmul : ∀ x ∈ J₁, t * x ∈ J) : W ∈ J.minimalPrimes ↔ W ∈ J₁.minimalPrimes := by
  have key : ∀ Q : Ideal S, Q.IsPrime → Q ≤ W → (J ≤ Q ↔ J₁ ≤ Q) := fun Q hQ hQW ↦
    ⟨fun h x hx ↦ (hQ.mem_or_mem (h (hmul x hx))).resolve_left fun htQ ↦ ht (hQW htQ), hJ.trans⟩
  simp only [Ideal.minimalPrimes, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hWp, hJW⟩, hmin⟩
    exact ⟨⟨hWp, (key W hWp le_rfl).mp hJW⟩, fun Q hQ hQW ↦ hmin ⟨hQ.1, (key Q hQ.1 hQW).mpr hQ.2⟩ hQW⟩
  · rintro ⟨⟨hWp, hJW⟩, hmin⟩
    exact ⟨⟨hWp, (key W hWp le_rfl).mpr hJW⟩, fun Q hQ hQW ↦ hmin ⟨hQ.1, (key Q hQ.1 hQW).mp hQ.2⟩ hQW⟩

end Local

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

end SectionCycle

end

end GroundTheory.Heights₂.Heights
