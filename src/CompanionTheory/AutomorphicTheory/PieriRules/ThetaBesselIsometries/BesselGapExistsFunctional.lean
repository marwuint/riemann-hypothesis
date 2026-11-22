import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentEstimate
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapIntegrability

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.FamilyDerivativeExpansion.BeL

theorem exists_normalised_bessel_map : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∃ l, IsBeL R z π μW μN l := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hside
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -⟩ := id hside
  obtain ⟨L, hL⟩ := hH.1.2.2.2 k r ε mu R Wp z u₀ π μW μN hDS hz hT hπ hW hN
  have hTK : ∀ v ∈ R.TK, v ∈ R.sm := (_root_.Gp91.GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS).2.2.2.2.1
  by_cases h0 : ∀ v ∈ R.TK, L v = 0
  · refine ⟨fun _ => 0, Formalism.FourierDecayAlt.P.DDSmoothness.bessel_zero, fun w hw v hv => ⟨(hL w hw v (hTK v hv)).1, ?_⟩⟩
    rw [(hL w hw v (hTK v hv)).2, h0 v hv]
    ext ξ
    simp
  · push Not at h0
    obtain ⟨v₀, hv₀, hne⟩ := h0
    have hB := Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul
      (_root_.Gp91.GlobalTheory.be_apply_isBes hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside v₀ hv₀ (L v₀)) (⟪L v₀, L v₀⟫_ℂ)⁻¹
    have e : ∀ w ∈ R.sm, (⟪L v₀, L v₀⟫_ℂ)⁻¹ • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v₀ (L v₀) = L w := by
      intro w hw
      rw [(hL w hw v₀ (hTK _ hv₀)).2, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
        inv_mul_cancel₀ (inner_self_ne_zero.2 hne), one_smul]
    refine ⟨_, hB, fun w hw v hv => ⟨(hL w hw v (hTK v hv)).1, ?_⟩⟩
    rw [(hL w hw v (hTK v hv)).2]
    simp only [e w hw, e v (hTK v hv)]

end CompanionTheory.FamilyDerivativeExpansion.BeL
