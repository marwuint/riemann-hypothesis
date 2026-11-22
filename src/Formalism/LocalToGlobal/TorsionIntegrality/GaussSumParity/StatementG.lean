import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementF
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.D

open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights (Integral frameJet frameJetOne nablaO)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog alG capG lsG deLoss dSet oddT)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def NRCM : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ s2 : MaximalUnramifiedExtension l, ‖s2‖ ≤ 1 ∧
    (∃ (c : ℂ) (hc : c ≠ 0), (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
      (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
      (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc))) ∧
    ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
    ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α

end Formalism.L2.Th1.D
