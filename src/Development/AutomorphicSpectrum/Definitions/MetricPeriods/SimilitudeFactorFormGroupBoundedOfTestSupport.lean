import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory GlobalTheory.CompanionTheory.Ar.PB Filter Topology

variable {Ψ : Type} [Fintype Ψ] {N e : ℕ}

abbrev LowEnt (Ψ : Type) (N : ℕ) : Type := Ψ × {p : Fin N × Fin N // p.2 < p.1}

end GlobalTheory.CompanionTheory.Ar.Cmp
