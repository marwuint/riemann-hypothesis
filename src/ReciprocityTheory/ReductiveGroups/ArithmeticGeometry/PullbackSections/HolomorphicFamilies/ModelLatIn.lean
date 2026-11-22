import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat
import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open scoped Pointwise

theorem absNorm_smul_eq {E : Type} [Field E] [NumberField E] (σ : E ≃ₐ[ℚ] E) (I : Ideal (𝓞 E)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (σ • I) (MulSemiringAction.toRingEquiv _ _ σ)
    (by rw [Ideal.pointwise_smul_def]; rfl)).toEquiv).symm

theorem bb_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := Formalism.L2.Pj.b_ne_bot D

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  haveI := D.host.galois
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr D.host.gal.toEquiv]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n, Formalism.HC.Frame.GG, Nat.card_prod]
  have h2 : Nat.card ℤˣ = 2 := by
    first
      | rw [Nat.card_eq_fintype_card, Int.card_units_eq_two]
      | simp
      | (rw [Nat.card_eq_fintype_card]; rfl)
      | (rw [Nat.card_eq_fintype_card]; decide)
  have hA : Nat.card D.R.MA = D.R.ord := by
    unfold Formalism.HC.Frame.MA
    rw [Nat.card_congr Multiplicative.toAdd]
    unfold Formalism.HC.Frame.A Formalism.HC.Idx
    exact Nat.card_fin _
  rw [h2, hA]
  ring

end ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI
