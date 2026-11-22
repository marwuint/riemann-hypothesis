import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelConditionEquivalent
import Formalism.GaussJetBounds.OneLetterGaussJets.OddLevelGainSum

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights (Integral frameJet frameJetOne nablaO)
open Formalism.DworkPowerSeriesWeights.OddLevelGainBounds (WcapOneLetter JnumOneLetter kaMaxOneLetter)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog alG capG lsG deLoss dSet oddT lamF InClass hhS uS sSub)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom Th alphaQ kernel4)

def ThetaFourthPowerShapeNormalised : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ ι : ℂ ≃+* ℂ_[l],
  ∃ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 →
    ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]),
    IsFrameH σ ι g₁ γ B' → uniformGaussModelCondition l g2 g3 s2 ε (thetaH l ι B' h t θ) γ

def FrobExistsH : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ

end Formalism.L2.Th1.Top
