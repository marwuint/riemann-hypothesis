import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.ThetaInZIsThetaLog
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.D

open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights (Integral frameJet frameJetOne nablaO)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog alG capG lsG deLoss dSet oddT)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def FieldDataCM : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
    ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ ∧
      (∃ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F) ∧
      ∀ d : ℕ, [NeZero d] → Even d → ∃ (ζ : MaximalUnramifiedExtension l) (om oms : Fin (d / 2) → MaximalUnramifiedExtension l),
        IsPrimitiveRoot ζ (l ^ d - 1) ∧ OwOK d σ om oms ∧ TrDual d σ om oms

end Formalism.L2.Th1.D
