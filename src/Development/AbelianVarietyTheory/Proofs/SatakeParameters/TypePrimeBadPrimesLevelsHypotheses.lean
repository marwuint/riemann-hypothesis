import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeFactsAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelJets

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)

noncomputable section

namespace GlobalTheory.DatumJets

def SplitSet {X : Fields} (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p : ℕ) : Prop :=
  X.Ok ∧ A.LaHyp a b S ∧ A.AA ≠ ⊥ ∧ A.ESmooth a b ∧ p.Prime ∧ ϖ * X.conjO ϖ = (p : 𝓞 X.E) ∧ IsCoprime ϖ (X.conjO ϖ) ∧
    ∀ P : HeightOneSpectrum (𝓞 X.E), ϖ ∈ P.asIdeal → P ∈ S

def PlaceAbove : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 K)),
    (p : 𝓞 K) ∈ w.asIdeal →
    ∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k : K, GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt lam (σ k) ↔ w.valuation K k ≤ 1

def TypePrimeBadPrimesLevelsHypotheses : Prop :=
  ∀ (D : D7) (EX : ErrX D) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) (δ : ℂ)
    (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), HostTie EX → IsSel (recFields D) sel →
    ∀ (i : Fin 2) (u : (recPrimes EX).Word) (mu : Tup (recFields D).F (recFields D).E (recFields D).K (badS D))
      (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel mu)), cst.Ok →
    ∀ a b : ℕ, (ambOf (recSeam D) B χ cD).LaHyp a b ∅ → (ambOf (recSeam D) B χ cD).ESmooth a b →
      SplitSet (ambOf (recSeam D) B χ cD) a b (Sall sel mu u) ((recFields D).conjO ((recPrimes EX).piG i))
        ((recPrimes EX).g i) ∧
      0 < cAof sel mu cst ∧ 0 < cBof sel mu cst u ∧ (recPrimes EX).g i ∣ cBof sel mu cst u

end GlobalTheory.DatumJets
