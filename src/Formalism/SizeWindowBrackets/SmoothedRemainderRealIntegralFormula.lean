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

instance neZeroHostN (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] : NeZero (hostN e q d) :=
  ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) (Fact.out : q.Prime).ne_zero)
    (Fact.out : d.Prime).ne_zero⟩

def condOf (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (ψ : AddChar (E0 × HA e) ℂ) : ℕ :=
  (dirChar (recMap e q d) ψ).conductor

instance neZeroCondOf (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (ψ : AddChar (E0 × HA e) ℂ) :
    NeZero (condOf e q d ψ) :=
  ⟨DirichletCharacter.conductor_ne_zero _⟩

end Formalism.LFunctionChainParameters.LBr2
