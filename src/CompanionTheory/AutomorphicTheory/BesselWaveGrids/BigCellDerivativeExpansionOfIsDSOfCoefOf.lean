import CompanionTheory.AutomorphicTheory.BesselWaveGrids.FamilyThroughDiscreteSeries

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset CompanionTheory.WaveGrid.Ball
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.WaveGrid.BallW

def CoefOf {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (R : Rep k r) (F : Mx k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (l : R.H → Wp) (l' : R.H → Wq), ∃ s, IsCoef R l l' F s

end CompanionTheory.WaveGrid.BallW
