import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun

noncomputable section

namespace GlobalTheory.FlatLine.Model

open NumberField IsDedekindDomain Module AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

def rescale {Z : Comp Xo c} {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ) (x' : ℝ) :
    ConstSec U x' Z la δ :=
  { s with
    cInf := (fun _ => lieFacZ Dw x' (wtOf Dw la 0) / lieFacZ Dw x (wtOf Dw la 0)) * s.cInf
    cInf_pos := fun σ => mul_pos (div_pos (lieFacZ_pos _ _) (lieFacZ_pos _ _)) (s.cInf_pos σ)
    norm_inf := fun σ => image_eq_singleton_iff.2 ⟨(s.hasPts.1 σ).1, fun z hz => by
      have := (lieFacZ_pos (Dw := Dw) x (wtOf Dw la 0)).ne'
      rw [Pi.mul_apply, ← s.homN_eq hz, homN, homN]; field_simp⟩ }

theorem sum_flatWt (τ : Psi H) :
    ∑ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) = Dw.q - Dw.p := by
  classical
  have hne : τ.1 ≠ conjEmb τ.1 := fun h => conj_not_mem τ (h ▸ τ.2)
  have key : ∀ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) =
      (if ρ = conjEmb τ.1 then (Dw.q : ℝ) else 0) - if ρ = τ.1 then (Dw.p : ℝ) else 0 := fun ρ => by
    by_cases h : ρ (H.rt : E) = H.rt0
    · have hm : Dw.mult ρ = Dw.p := by simp [Datum.mult, h]
      have h1 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = τ.1 then -1 else 0 :=
        fun i => by
          have := wtOf_big (flatWt Dw τ) 0 ⟨ρ, h⟩ i (hm ▸ i.2)
          rw [this]
          simp [flatWt, parWt, Subtype.ext_iff]
      simp only [h2]
      split_ifs <;> simp_all
    · have hm : Dw.mult ρ = Dw.q := by simp [Datum.mult, h]
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = conjEmb τ.1 then 1 else 0 :=
        fun i => by
          have := wtOf_small (flatWt Dw τ) 0 ⟨_, conj_mem h⟩ i (hm ▸ i.2)
          simp only [conjEmb_conjEmb] at this
          rw [this]
          by_cases e : ρ = conjEmb τ.1
          · simp [flatWt, parWt, Subtype.ext_iff, e, conjEmb_conjEmb]
          · have : conjEmb ρ ≠ τ.1 := fun e' => e (by rw [← e', conjEmb_conjEmb])
            simp [flatWt, parWt, Subtype.ext_iff, e, this]
      simp only [h2]
      split_ifs <;> simp_all
  simp [key]

end GlobalTheory.FlatLine.Model
