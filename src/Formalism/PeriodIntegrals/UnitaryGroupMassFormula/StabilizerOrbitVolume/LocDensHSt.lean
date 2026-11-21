import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.PosNear
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.WeilQuotMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotMeasUniq

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def FibLatGen : Prop :=
  ∀ (V X Y : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    ∀ (f : V → Y) (ι : X → Y), Function.Injective ι → ∀ (G : V → X), Continuous G →
    (∀ x, f x = ι (G x)) → ∀ (U : Set V) (B : Set X) (fib : X → Measure V),
    IsFibreFamily μ f ι U ν B fib → ∀ (T : X), B ∈ 𝓝 T →
    ∀ (L : AddSubgroup V), IsOpen (L : Set V) → IsCompact (L : Set V) →
    ∀ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X), Λ 0 ≤ L →
      (∀ n, IsOpen (Λ n : Set V)) → (∀ n, IsCompact (Λ n : Set V)) → Antitone Λ →
      (∀ n, IsOpen (H n : Set X)) → (∀ n, IsCompact (H n : Set X)) →
      (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') →
    ∀ (P : Set V), P ⊆ L → (∀ y ∈ P, ∀ Z ∈ Λ 0, y + Z ∈ P) → IsOpen P → IsClosed P →
    ∀ Nb ∈ 𝓝 T, (∀ x ∈ P, G x ∈ Nb → x ∈ U) →
      (∀ y ∈ P, G y - T ∈ H 0 → ∃ D : V →+ X, (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) →
      ∫ x, P.indicator (1 : V → ℂ) x ∂(fib T) =
        (((μ (P ∩ G ⁻¹' {z | z - T ∈ H 0})) / ν (H 0)).toReal : ℂ)

end PI.VolStabSW
