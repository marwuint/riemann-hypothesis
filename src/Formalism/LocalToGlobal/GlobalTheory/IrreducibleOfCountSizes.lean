import Formalism.LocalToGlobal.GlobalTheory.FamCol
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.GlobalTheory.AnalyticConclusionCompatibleMeanSquare
import Formalism.SizeWindowBrackets.PrimeClassLossHypothesesSatisfiable
import Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBridge
import Formalism.PadicSubsetSums.CentralIdempotents.StretchedExponentialDominance
import Formalism.SharpRestriction.LevelLetterCocycles.CylinderCountFamily

open NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ConcN

open Formalism Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.FamCol

def NumbersAt (x ε εC C W₁ W₂ : ℝ) : Prop :=
  0 ≤ εC ∧ εC ≤ 1 / 2 ∧ W₁ ≤ x ^ C * Real.exp (-(x ^ (ε / 6))) ∧ W₂ ≤ x ^ C * Real.exp (-(x ^ (ε / 6)))

def NumbersDominantLarge : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ C ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop, ∀ εC W₁ W₂ : ℝ,
    NumbersAt x ε εC C W₁ W₂ → (1 + εC) / (1 - εC) * (W₁ + W₂) ≤ LChain6.E7 x ε

def Wg (f m N g q₁ d : ℕ) : ℝ :=
  3 * (f : ℝ) / (g : ℝ) +
    23 * (f : ℝ) * Real.log (g : ℝ) / Real.sqrt (g : ℝ) +
    2 * (f : ℝ) * (m : ℝ) * (1 / (4 * ((min q₁ d : ℕ) : ℝ)) + (1 + Real.log (N : ℝ)) / ((g : ℝ) - 1)) +
    (N : ℝ) / 2 * (7 / 8 : ℝ) ^ f +
    Real.exp (-(f : ℝ) / (5 * Real.log (N : ℝ)))

def epsC (c : ℝ) (N f : ℕ) : ℝ := Real.exp (-(c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ)))

def SizesAt (x ε Cs : ℝ) (f m N g q₁ d : ℕ) : Prop :=
  Real.exp (8 * x ^ ε) ≤ (g : ℝ) ∧ x ^ 2 ≤ (f : ℝ) ∧ (f : ℝ) ≤ x ^ Cs ∧ (m : ℝ) ≤ x ^ Cs ∧
    100 ≤ N ∧ (N : ℝ) ≤ x ^ Cs ∧ Real.exp (x ^ (ε / 6)) ≤ ((min q₁ d : ℕ) : ℝ)

def WeightNumbersBound : Prop :=
  ∀ ε Cs : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x : ℝ in Filter.atTop, ∀ f m N g q₁ d : ℕ,
    SizesAt x ε Cs f m N g q₁ d → Wg f m N g q₁ d ≤ x ^ (3 * Cs + 3) * Real.exp (-(x ^ (ε / 6)))

def EpsilonBoundLargeX : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ x : ℝ in Filter.atTop, ∀ N f : ℕ, 100 ≤ N → x ^ 2 ≤ (f : ℝ) → epsC c N f ≤ 1 / 2

section Rec

open Formalism.BasicNotions Formalism.MainNotions

def SizesRec (D : D7) (x ε Cs : ℝ) : Prop :=
  ∀ j : Fin 2, SizesAt x ε Cs D.R.f D.R.m D.R.r (D.host.g j) D.host.q D.host.d

end Rec

section AllRowsIn

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders

def DstarE {D : D7} (A : AllRows D) (e : A.B.I.Gf → ℂ) : ℝ :=
  A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund e

def CountAllRows {D : D7} (A : AllRows D) (εC : ℝ) : Prop :=
  0 ≤ εC ∧ εC < 1 ∧ 0 < DstarE A A.B.e ∧
    ∀ (k : Fin 2) (S : Set (Tup D k)),
      |(A.dimT (cyl D k S) : ℝ) - DstarE A (A.eT (cyl D k S))| ≤ εC * DstarE A (A.eT (cyl D k S))

def WeightAllRows {D : D7} (A : AllRows D) : Prop :=
  (∀ (k : Fin 2) v f, 0 ≤ wtOf D k (A.eVec k v) f) ∧
    ∀ (k : Fin 2) (S : Finset (Tup D k)), (∀ t ∈ S, ¬ goodAt D k t) →
      locShare D A.eVec k S ≤ Wg D.R.f D.R.m D.R.r (D.host.g k) D.host.q D.host.d

def FamilyIrreducibleOfCountWeightSizes : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ (eps Cs c : ℝ), 0 < eps → eps ≤ 1 → 0 < c → ∀ (Fm : FamP eps),
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i),
      LabelCountGoodInjective A ∧
      CountAllRows A (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) ∧
      WeightAllRows A ∧
      SizesRec (Fm.D x i) x Fm.ez Cs) →
    LinkIRR Fm

end AllRowsIn

end Formalism.L2.GlobalTheoryTheory.ConcN
