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

def parPt (Lp : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ_[p]) (z : ℂ) : ℂ_[p] :=
  if z ∈ Lp.lattice then 0 else
    let x₀ : ℂ_[p] := lamC lam (Lp.weierstrassP z)
    let y₀ : ℂ_[p] := lamC lam (Lp.derivWeierstrassP z / 2)
    let x : ℂ_[p] := (x₀ - C.r) / (C.u : ℂ_[p]) ^ 2
    let y : ℂ_[p] := (y₀ - C.s * (x₀ - C.r) - C.t) / (C.u : ℂ_[p]) ^ 3
    (-x) / y

variable {D}

end Curve

section Meas

variable {p : ℕ} [Fact p.Prime]

abbrev Meas (p r : ℕ) [Fact p.Prime] : Type := C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p]

def IsRMeas {r : ℕ} (μ : Meas p r) : Prop := ‖μ‖ ≤ 1

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
