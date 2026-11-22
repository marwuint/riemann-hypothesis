import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildEqOneOfCharpolyUnipotentModL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildInertiaKilledByAdditiveLocallyConstant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.WildSetSQ

theorem char_eq_one_of_wild {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (had : IsAdic (IsLocalRing.maximalIdeal O)) (χ : G E Ω →* Oˣ)
    (hχ : Continuous fun g => ((χ g : Oˣ) : O)) (σ : G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1)
    (h : χ σ ^ m = 1) : χ σ = 1 := by
  have key : ∀ M : ℕ, ((χ σ : Oˣ) : O) - 1 ∈ IsLocalRing.maximalIdeal O ^ M := by
    intro M
    let H : Subgroup (G E Ω) :=
      ((Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ M)).toMonoidHom).comp χ).ker
    have hH : ∀ g, g ∈ H ↔ ((χ g : Oˣ) : O) - 1 ∈ IsLocalRing.maximalIdeal O ^ M := by
      intro g
      rw [← Ideal.Quotient.eq, map_one, MonoidHom.mem_ker, Units.ext_iff]
      rfl
    have ho : IsOpen (H : Set (G E Ω)) := by
      have e : (H : Set (G E Ω)) = (fun g => ((χ g : Oˣ) : O) - 1) ⁻¹'
          ((IsLocalRing.maximalIdeal O ^ M : Ideal O) : Set O) := by
        ext g
        exact hH g
      rw [e]
      exact ((isAdic_iff.1 had).1 M).preimage (hχ.sub continuous_const)
    refine (hH σ).1 (GlobalTheory.WildKill.mem_of_wild A H ho σ m hm hσ ?_)
    rw [hH, map_pow, h, Units.val_one, sub_self]
    exact zero_mem _
  rw [Units.ext_iff, Units.val_one, ← sub_eq_zero]
  have h2 := Ideal.mem_iInf.2 key
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top] at h2
  simpa using h2

theorem coprime_pred (g : ℕ) (hg : 1 ≤ g) : (g - 1).Coprime g := by
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  simp

end GlobalTheory.WildSetSQ

namespace GlobalTheory.WildSetSQ

end GlobalTheory.WildSetSQ

namespace GlobalTheory.WildSetSQ

end GlobalTheory.WildSetSQ
