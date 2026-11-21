import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecond

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.MovedDatum

section Gen

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem norm_unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (h : IsUnit (redP P a)) (σ : K →+* ℂ) :
    ‖σ (LocE.unitV χ a)‖ = 1 := by
  unfold LocE.unitV
  rw [dif_pos h]
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hc : 0 < Nat.card (𝓞 E ⧸ P.asIdeal)ˣ := Nat.card_pos
  have h1 : ((χ h.unit : Kˣ) : K) ^ Nat.card (𝓞 E ⧸ P.asIdeal)ˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have h2 : ‖σ ((χ h.unit : Kˣ) : K)‖ ^ Nat.card (𝓞 E ⧸ P.asIdeal)ˣ = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hc.ne').1 h2

variable [StarRing E]

theorem locSmall_om {a b : ℕ} {e e' : ℕ → ℤ} (cq sq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {g : Sp E a ≃ₗ[E] Sp E a} {g' : Sp E b ≃ₗ[E] Sp E b}
    (hg : g ∈ stabL E a (LocE.sclLat P (qOf P) a e)) (hg' : g' ∈ stabL E b (LocE.sclLat P (qOf P) b e'))
    {Φ : HomE E a b → K} {β : ℝ}
    (hΦ : LocSmall (qOf P) (LocE.sclLat P (qOf P) a e) (LocE.sclLat P (qOf P) b e') Φ β) :
    LocSmall (qOf P) (LocE.sclLat P (qOf P) a e) (LocE.sclLat P (qOf P) b e')
      (Loc.om (LocE.locChar (qOf P) cq χ) (LocE.vP P (qOf P)) sq g g' Φ) β := by
  have hu := GlobalTheory.LastSteps.isUnit_det_of_stab hg
  have hu' := GlobalTheory.LastSteps.isUnit_det_of_stab hg'
  obtain ⟨h1, h2, h3⟩ := hΦ
  refine ⟨fun x hx y hy => ?_, fun x z hz => ?_, fun σ x => ?_⟩
  · unfold Loc.om at hx
    have h4 := h1 _ (right_ne_zero_of_mul hx) (g.symm y) ((hg _).1 (by simpa using hy))
    have h5 := (hg' _).2 h4
    simpa using h5
  · unfold Loc.om
    congr 1
    have h4 := h2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) (g'.symm.toLinearMap ∘ₗ z ∘ₗ g.toLinearMap) fun y hy =>
      (hg' _).1 (by simpa using hz _ ((hg y).2 hy))
    rw [← h4]
    congr 1
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]
  · unfold Loc.om
    rw [GlobalTheory.LastSteps.locChar_unit cq χ hu, GlobalTheory.LastSteps.locChar_unit cq χ hu', GlobalTheory.LastSteps.vP_unit hu,
      GlobalTheory.LastSteps.vP_unit hu']
    simp only [neg_zero, zero_mul, zpow_zero, mul_one, map_mul, map_inv₀, norm_mul, norm_inv, norm_unitV χ hu,
      norm_unitV χ hu', inv_one, one_mul]
    exact h3 σ _

end Gen

end GlobalTheory.ColNorms.MovedDatum
