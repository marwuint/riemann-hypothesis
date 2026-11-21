import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP
import Formalism.ZeroFreeRegion.Statement
import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

open Finset Filter Topology ArithmeticFunction

noncomputable section

namespace Formalism.LFunctionChainParameters.LBr2

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds

def X1 (ε x : ℝ) : ℝ := Real.exp (x ^ (ε / 5))

def X2 (ε x : ℝ) : ℝ := Real.exp (x ^ (ε / 5) * Real.log x ^ 2)

def logDerivLAtOne {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1

def Gchi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((y / n - 1 : ℝ) : ℂ)) + (y : ℂ) * logDerivLAtOne χ

def qc (q : ℕ) [Fact q.Prime] : DirichletCharacter ℂ q :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)

def chi8 : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

def one1 : DirichletCharacter ℂ 1 := 1

instance neZeroMulPrime {t q : ℕ} [NeZero t] [Fact q.Prime] : NeZero (t * q) :=
  ⟨Nat.mul_ne_zero (NeZero.ne t) (Fact.out : q.Prime).ne_zero⟩

def tw {t : ℕ} (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime] : DirichletCharacter ℂ (t * q) :=
  DirichletCharacter.changeLevel (Dvd.intro q rfl) θ * DirichletCharacter.changeLevel (Dvd.intro_left t rfl) (qc q)

def ZeroFreeBox {N : ℕ} [NeZero N] (Q : ℝ) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → DirichletCharacter.LFunction χ s ≠ 0

def GoodFor {N : ℕ} [NeZero N] (Q : ℝ) (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ (N : ℝ) ≤ Q ∧ ZeroFreeBox Q χ

def SplitsIn (d p : ℕ) : Prop :=
  ∃ r s : ZMod p, r ≠ s ∧ r ^ 2 - r + (((d + 1) / 4 : ℕ) : ZMod p) = 0 ∧ s ^ 2 - s + (((d + 1) / 4 : ℕ) : ZMod p) = 0

def ExistsSplitGoodPrimePair (ε C x : ℝ) : Prop :=
  ∃ (q₁ d : ℕ) (_ : Fact q₁.Prime) (_ : Fact d.Prime),
    q₁ % 8 = 3 ∧ d % 16 = 7 ∧
    X1 ε x ^ (1 / 2 : ℝ) < (q₁ : ℝ) ∧ (q₁ : ℝ) ≤ X1 ε x ∧ X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ X2 ε x ∧
    SplitsIn d q₁ ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (ε / 5) → SplitsIn d p) ∧
    GoodFor (8 * X1 ε x) (tw one1 q₁) ∧ GoodFor (8 * X1 ε x) (tw chi8 q₁) ∧
    GoodFor (8 * X1 ε x * X2 ε x) (tw one1 d) ∧ GoodFor (8 * X1 ε x * X2 ε x) (tw chi8 d) ∧
    GoodFor (8 * X1 ε x * X2 ε x) (tw (tw one1 q₁) d) ∧ GoodFor (8 * X1 ε x * X2 ε x) (tw (tw chi8 q₁) d) ∧
    (‖Gchi (tw one1 q₁) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw one1 q₁)‖ ≤ C * Real.log x) ∧
    (‖Gchi (tw one1 d) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw one1 d)‖ ≤ C * Real.log x) ∧
    (‖Gchi (tw (tw one1 q₁) d) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw (tw one1 q₁) d)‖ ≤ C * Real.log x)

instance neZeroHostN (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] : NeZero (hostN e q d) :=
  ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) (Fact.out : q.Prime).ne_zero)
    (Fact.out : d.Prime).ne_zero⟩

def condOf (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (ψ : AddChar (E0 × HA e) ℂ) : ℕ :=
  (dirChar (recMap e q d) ψ).conductor

instance neZeroCondOf (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (ψ : AddChar (E0 × HA e) ℂ) :
    NeZero (condOf e q d ψ) :=
  ⟨DirichletCharacter.conductor_ne_zero _⟩

def LogNE : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ n q₁ d : ℕ, 1 ≤ n → (n : ℝ) ≤ x ^ A →
    X1 ε x ^ (1 / 2 : ℝ) < (q₁ : ℝ) → (q₁ : ℝ) ≤ X1 ε x → X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) → (d : ℝ) ≤ X2 ε x →
    x ^ (ε / 5) / 2 < Real.log q₁ ∧ Real.log q₁ ≤ x ^ (ε / 5) ∧
    x ^ (ε / 5) * Real.log x ^ 2 / 2 < Real.log d ∧ Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2 ∧
    Real.log ((4 * n * q₁ * d : ℕ) : ℝ) ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2

def NoRealZeroSmall : Prop :=
  (∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0) ∧
  (∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction chi8 (σ : ℂ) ≠ 0)

end Formalism.LFunctionChainParameters.LBr2
