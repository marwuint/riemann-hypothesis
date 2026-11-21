import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem

open NumberField Formalism.MainNotions.S

def CountingTheorem : Prop :=
  ∀ Cg : ℝ, ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    GlobalTheory.Count.CountHyp B Cg n₀ d p q b →
      FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
        |(B.D : ℝ) - GlobalTheory.Count.mainTerm B d| ≤
          Real.exp (-(1 / 16 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) *
            GlobalTheory.Count.mainTerm B d

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem
