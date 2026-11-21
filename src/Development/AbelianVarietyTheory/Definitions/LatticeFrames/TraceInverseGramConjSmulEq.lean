import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.Model

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')

include l in
theorem tau_gram (h : IsLineVec L' ζ') :
    l.τᴴ * (B.L.gram * l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have hn := l.norm
  have hm : B.ζ = -(l.τ *ᵥ ζ') := by rw [l.map, neg_neg]
  have h0 := h.2
  rw [hm, star_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, Matrix.star_mulVec, ← dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc] at hn
  refine Matrix.ext fun i j => ?_
  obtain rfl := Subsingleton.elim i default
  obtain rfl := Subsingleton.elim j default
  generalize l.τᴴ * (B.L.gram * l.τ) = M at hn ⊢
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique, Pi.star_apply] at hn h0
  have hz : ζ' default ≠ 0 := fun e => h0 (by rw [e]; simp)
  have hz' : star (ζ' default) ≠ 0 := star_ne_zero.2 hz
  rw [Matrix.smul_apply, smul_eq_mul]
  apply mul_right_cancel₀ hz
  apply mul_left_cancel₀ hz'
  rw [hn]; ring

end GlobalTheory.Unf.Model

end
