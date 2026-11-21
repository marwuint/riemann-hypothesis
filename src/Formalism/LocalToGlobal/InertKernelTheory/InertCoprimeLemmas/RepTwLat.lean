import Formalism.LocalToGlobal.InertKernelTheory.FrameLatMap
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrob
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts

noncomputable section

open scoped Matrix

namespace Formalism.L2.KerInert.RepTwLat

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.KerInert.RepFrame
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Defs

variable (D : D7)

def IntAtP (p : ℕ) (e : D.host.E) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def hStd {N : ℕ} (x y : Fin N → D.host.E) : D.host.E := ∑ k, D.host.conj (x k) * y k

def SelfDualP (p : ℕ) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, IntAtP D p (hStd D x y)) ∧
  ∀ y : Fin N → D.host.E, (∀ x ∈ L, IntAtP D p (hStd D x y)) → ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) • y ∈ L

def locSpan (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] (ρ : D.host.E →+* K) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Submodule R (Fin N → K) :=
  Submodule.span R ((fun x : Fin N → D.host.E => fun k => ρ (x k)) '' (L : Set (Fin N → D.host.E)))

end Defs

end Formalism.L2.KerInert.RepTwLat

set_option pp.fullNames true
