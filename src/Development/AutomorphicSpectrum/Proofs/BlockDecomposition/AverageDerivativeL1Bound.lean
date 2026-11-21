import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def avg {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (h : ℝ → ℝ) (u : ℝ → Mat n → V) : Mat n → V :=
  fun x => ∫ t, (h t : ℂ) • u t x

section Norms

variable [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]

def ip [InnerProductSpace ℂ V] (f h : Mat n → V) : ℂ := ∫ y : G n, ⟪f y.val, h y.val⟫_ℂ ∂μ

end Norms

def WaveUniq : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → (∀ g ∈ GLs n, u 0 g = v 0 g) →
    ∀ t, ∀ x ∈ GLs n, u t x = v t x

end GlobalTheory.CompanionTheory.WaveK
