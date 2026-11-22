import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical
open Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

section Curve

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

def atP (c : D.host.K) : ℂ_[p] := lamC lam (D.host.φ₀ (c : D.host.E))

variable {D}

end Curve

section Meas

variable {p : ℕ} [Fact p.Prime]

abbrev Meas (p r : ℕ) [Fact p.Prime] : Type := C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p]

def wt {r : ℕ} (f : C(Fin r → ℤ_[p], ℂ_[p])) (μ : Meas p r) : Meas p r :=
  μ.comp (ContinuousLinearMap.mul ℂ_[p] C(Fin r → ℤ_[p], ℂ_[p]) f)

theorem wt_apply {r : ℕ} (f g : C(Fin r → ℤ_[p], ℂ_[p])) (μ : Meas p r) : wt f μ g = μ (f * g) := rfl

variable (D : D7) {N N' r : ℕ} (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

end Meas

section Lifts

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}

def vecOf (A : Matrix (Fin N') (Fin N) D.host.E) : VC D N N' := δ • embV D (tor0 D cc δ) A

end Lifts

end GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership
