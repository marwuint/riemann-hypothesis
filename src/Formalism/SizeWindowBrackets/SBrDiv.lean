import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
import Formalism.LogFactorialIndices.StatementSize
import Formalism.HarderNarasimhan.QuotRealize

open Module NumberField IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LBrDiv

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

def ThmDiv : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]

    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)

    (x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' dC lam0 C0 : ℝ)

    (Lpass Eb e6 eP logOm : ℝ) (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam →
    (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
    (∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →

    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →

    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →

    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →

    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η → 1 ≤ dC →

    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →

    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →

    lam0 ≤ b → N ^ 2 * dC ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →

    0 ≤ C0 →
    Lpass ≤ 1 + C0 * lam0 →
    Eb ≤ C0 * m * xe * (B0 + Nc) →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * (La + dC) + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)

def ThmConcl {Pl : Type} (TT : Finset Pl) (aT : Pl → ℝ)
    (muC hu Fo logT logOm m a La B0 Nc xe C0 : ℝ) : Prop :=
  muC + hu - 2 * Fo ≤
    ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
    (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)

def TypePrimeCostDeviationBound {J Pl : Type} [Fintype J] (TT : Finset Pl) (aT : Pl → ℝ) (sE : J → ℝ) (lg m B0 C0 : ℝ) : Prop :=
  (∀ j, |2 * sE j - (∑ t ∈ TT, aT t) * lg| ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * B0) ∧
  |2 * (∑ j, sE j) - m * ((∑ t ∈ TT, aT t) * lg)| ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * (m * B0)

def CorrectedHeightVariationBound {U Pl : Type} (TT : Finset Pl) (hu logT : U → ℝ) (aT : U → Pl → ℝ) (a La B0 m C0 : ℝ) : Prop :=
  ∀ u u', |(hu u + ∑ t ∈ TT, aT u t * logT u) - (hu u' + ∑ t ∈ TT, aT u' t * logT u')| ≤
    (7 * C0 ^ 2 + 18) * ((TT.card : ℝ) * a * La + m * B0)

section Defs4
variable {K : Type} [Field K] [NumberField K]

def lw (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ) / (finrank ℚ K : ℝ)

def lcv [StarRing K] {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (L : Submodule (𝓞 K) (Fin d → K)) : ℝ :=
  (2 / (finrank ℚ K : ℝ)) * Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X L)

def plOf (w : HeightOneSpectrum (𝓞 K)) : slopeLatticeData.FinPl K := ⟨w.asIdeal, w.isMaximal⟩

end Defs4

def RowsAreDual {I : Type} {m : ℕ} (F : Fam I m) {D : ℕ} (XE : InfinitePlace F.K → Matrix (Fin D) (Fin D) ℂ)
    (R : Submodule (𝓞 F.K) (Fin D → F.K)) (ψ : Module.Dual F.K (Fin D → F.K) →ₗ[F.K] F.Wd) : Prop :=
  Function.Injective ψ ∧
  (∀ v x, Formalism.HermitianLatticesTheory.normAt F.b' F.X' v (ψ x)
    = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) v x) ∧
  F.cc = (dualLat R).map (ψ.restrictScalars (𝓞 F.K))

end Formalism.LFunctionChainParameters.LBrDiv
