import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasSubstEv

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.BiadditiveBalancedSeries

section Types

variable {E : Type} [Field E] [NumberField E]
variable {k : Type} [Field k]

def conjEmb [IsCMField E] (τ : E →+* k) : E →+* k :=
  τ.comp (IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E).toRingEquiv.toRingHom

def lieEig [StarRing (𝓞 E)] {R : Type} [CommRing R] [Algebra R k] {d : ℕ}
    (B : FB R d (𝓞 E)) (τ : E →+* k) : Submodule k (Fin d → k) where
  carrier := {v | ∀ a : 𝓞 E, (dAct k B a).mulVec v = τ (a : E) • v}
  add_mem' := by
    intro v w hv hw a
    rw [Matrix.mulVec_add, hv a, hw a, smul_add]
  zero_mem' := by
    intro a
    rw [Matrix.mulVec_zero, smul_zero]
  smul_mem' := by
    intro c v hv a
    rw [Matrix.mulVec_smul, hv a, smul_comm]

def IsHarmonic [IsCMField E] (r : (E →+* k) → ℕ) {n : ℕ}
    (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k) : Prop :=
  ∀ (τ : E →+* k) (i : Fin (r τ)) (i' : Fin (r (conjEmb τ))),
    ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* k, Fin (r τ)), b)
      (MvPolynomial.pderiv ((⟨conjEmb τ, i'⟩ : Σ τ : E →+* k, Fin (r τ)), b) P) = 0

end Types

end GlobalTheory.IndefiniteRowSideFullHecke.BiadditiveBalancedSeries
