import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.TowerOfAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.MainNotions.DIV.Cons (SCF intO)
open Formalism.L2.Pj.PointsOfFlagModel

namespace GlobalTheory.IntegralPointCheck

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {p : ℕ} {Y : Model Xo c β} {C : SCF p}

def embHom (P : PtC Y C) (τ : E →+* ℂ) : 𝓞 E →+* ↥C.S :=
  P.fK.comp ((τ.comp (algebraMap (𝓞 E) E)).codRestrict c.F.toSubring (fun a => c.conj τ a))

theorem embHom_apply (P : PtC Y C) (τ : E →+* ℂ) (a : 𝓞 E) : embHom P τ a = P.emb τ a := rfl

theorem valuationRing_intO (K : Type) [NormedField K] [IsUltrametricDist K] : ValuationRing (intO K) := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  rcases le_total ‖(a : K)‖ ‖(b : K)‖ with h | h
  · by_cases hb : (b : K) = 0
    · refine ⟨0, Or.inl (Subtype.ext ?_)⟩
      simp [hb]
    · refine ⟨⟨a / b, ?_⟩, Or.inr (Subtype.ext ?_)⟩
      · change ‖(a : K) / b‖ ≤ 1
        rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · change (b : K) * (a / b) = a
        field_simp
  · by_cases ha : (a : K) = 0
    · refine ⟨0, Or.inr (Subtype.ext ?_)⟩
      simp [ha]
    · refine ⟨⟨b / a, ?_⟩, Or.inl (Subtype.ext ?_)⟩
      · change ‖(b : K) / a‖ ≤ 1
        rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · change (a : K) * (b / a) = b
        field_simp

theorem isFractionRing_intO (K : Type) [NormedField K] [IsUltrametricDist K] : IsFractionRing (intO K) K := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  rcases le_total ‖z‖ 1 with h | h
  · exact ⟨⟨z, h⟩, 1, by simp; rfl⟩
  · refine ⟨1, ⟨z⁻¹, ?_⟩, ?_⟩
    · change ‖z⁻¹‖ ≤ 1
      rw [norm_inv]; exact inv_le_one_of_one_le₀ h
    · change z = ((1 : intO K) : K) / z⁻¹
      simp

end GlobalTheory.IntegralPointCheck
