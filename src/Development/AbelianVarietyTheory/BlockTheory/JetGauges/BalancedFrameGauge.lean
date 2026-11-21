import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.BalancedFrameGauge

section Letters

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def conjType {k : Type} [Field k] (τ : E →+* k) : E →+* k :=
  τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom

variable {E}

def lieEigen {R : Type} [CommRing R] {d : ℕ} [StarRing (𝓞 E)] (k : Type) [Field k] [Algebra R k]
    (B : FB R d (𝓞 E)) (τ : E →+* k) : Submodule k (Fin d → k) where
  carrier := {v | ∀ a : 𝓞 E, (dAct k B a).mulVec v = τ (a : E) • v}
  add_mem' := fun {v w} hv hw a => by
    rw [Matrix.mulVec_add, hv a, hw a, smul_add]
  zero_mem' := fun a => by simp
  smul_mem' := fun c v hv a => by
    rw [Matrix.mulVec_smul, hv a, smul_comm]

def IsHarmonic {k : Type} [Field k] (r : (E →+* k) → ℕ) {n : ℕ}
    (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k) : Prop :=
  ∀ (τ : E →+* k) (i : Fin (r τ)) (i' : Fin (r (conjType E τ))),
    ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* k, Fin (r τ)), b)
      (MvPolynomial.pderiv ((⟨conjType E τ, i'⟩ : Σ τ : E →+* k, Fin (r τ)), b) P) = 0

end Letters

end GlobalTheory.IndefiniteRowSideFullHecke.BalancedFrameGauge
