import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLimDeg
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaDictionaryComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop
open scoped ENNReal

namespace GlobalTheory.CovHt

def cost {K : Type} [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ) (t : (K →+* ℂ) → ℝ) : ℝ :=
  ((e.sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ)) + ∑ σ, t σ) / (Module.finrank ℚ K : ℝ)

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7}
  (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def depthOn (Z : Comp Xo c) (G : WTZ E) (v : Rul Xo c → EReal) : EReal := ⨅ w ∈ latOn U Z G, v (w : Rul Xo c)

def smallL (Z : Comp Xo c) (G : WTZ E) (τ : ℕ) (t : ℝ) : Set (cuspOn U Z (τ • G)) :=
  {f | (∀ la, ∀ v ∈ (recVals Xo c).1 la, (τ : EReal) * depthOn U Z G v ≤ v (f : Rul Xo c)) ∧
    ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
      ENNReal.ofReal (homN (U σ) x (τ • G) f ⟨y.1, y.2.1⟩) ^ 2 ≤
        ENNReal.ofReal (Real.exp (2 * τ * t)) * bergOn (U σ) (V σ) (dict σ) Z G y ^ τ}

def volL (a : ℕ) (Z : Comp Xo c) (G : WTZ E) (t : ℝ) : ℝ≥0∞ :=
  countVol (dimFlag Dw) (Module.finrank ℚ c.F) a fun τ => (smallL U x V dict Z G τ t).encard

def FinBd (Z : Comp Xo c) (G : WTZ E) (a : ℕ) (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) : Prop :=
  ∀ la, ∀ v ∈ (recVals Xo c).1 la, (∃ w ∈ latOn U Z G, v (w : Rul Xo c) ≠ ⊤) →
    (a : EReal) * depthOn U Z G v ≤ v θ + ((a * e la : ℝ) : EReal)

def NoBase (Z : Comp Xo c) (G : WTZ E) : Prop :=
  ∀ la, ∀ v ∈ (recVals Xo c).1 la, ∀ G' : WTZ E, ∀ f ∈ cuspOn U Z G', v f ≠ ⊤ → ∃ w ∈ latOn U Z G, v (w : Rul Xo c) ≠ ⊤

def InfBd (Z : Comp Xo c) (G G₀ : WTZ E) (a : ℕ) (θ : Rul Xo c) (t : (c.F →+* ℂ) → ℝ) : Prop :=
  (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) ∧
  ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
    ENNReal.ofReal (homN (U σ) x G₀ θ ⟨y.1, y.2.1⟩) ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * a * t σ)) * bergOn (U σ) (V σ) (dict σ) Z G y ^ a

def Carries (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (θ : Rul Xo c) : Prop :=
  θ ∈ secZ Xo c (exOf Dw ((8 : ℤ) • (u - u')) 0) ∧ genVal Z θ ≠ 0 ∧
    ∀ (k : ℕ), ∀ f ∈ cuspOn U Z ((8 * k) • wtOf Dw u' 0), θ ^ k * f ∈ cuspOn U Z ((8 * k) • wtOf Dw u 0)

def Mult (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (cc : ℝ) : Prop :=
  NoBase U Z (wtOf Dw u 0) ∧ ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ),
    Carries U Z u u' θ ∧ FinBd U Z (wtOf Dw u 0) 8 θ e ∧
    InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - u')) 0) 8 θ t ∧ cost e t ≤ cc

def l1 (u : AllWt.Weight Dw) : ℝ := ∑ τ, ∑ i, |(u τ i : ℝ)|

variable (E) in

def htEx (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) + 40 * ((padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ))

variable (Xo c) in

def HTCmp : Prop := ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal →
  ∀ v ∈ (recVals Xo c).1 la, ∃ w ∈ (htVals Xo c).1 la, ∀ (u : AllWt.Weight Dw), ∀ f ∈ secZ Xo c (exOf Dw u 0),
    w f ≤ v f + (((vLa la (p : c.F) : ℝ) * htEx E p * l1 u : ℝ) : EReal)

variable (l) in

def htCost (B : ℝ) : ℝ := ∑ᶠ p ∈ htPrimes l B, htEx E p * Real.log p

def WtGap (u : AllWt.Weight Dw) (g : ℝ) : Prop :=
  0 < g ∧ (∀ τ, StrictAnti (u τ)) ∧ ∀ τ (a b : Fin (Dw.p + Dw.q)), Dw.p ≤ (a : ℕ) → a ≠ b → g ≤ |(u τ a : ℝ) - u τ b|

def bndB (u : AllWt.Weight Dw) (g : ℝ) : ℝ :=
  4 * (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (1 + (⨆ k : Psi H × Fin (Dw.p + Dw.q), |(u k.1 k.2 : ℝ)|) / g)

def errX (s : ℝ) (u : AllWt.Weight Dw) (g : ℝ) : ℝ :=
  (Real.log (bndB u g) + s) * l1 u + (Dw.q : ℝ) * ∑ τ, ((⨆ i, (u τ i : ℝ)) - ⨅ i, (u τ i : ℝ))

def MeanGe (u : AllWt.Weight Dw) (B X : ℝ) : Prop :=
  ∃ sl : Comp Xo c → ℝ, (∀ Z, (sl Z : EReal) ≤ compVolSlope U x 8 (mixVals Xo c B) Z u) ∧
    -X ≤ (∑ᶠ Z, sl Z) / (Nat.card (Comp Xo c) : ℝ)

def MeanAll (s C : ℝ) : Prop := ∀ (u : AllWt.Weight Dw) (g : ℝ), WtGap u g → MeanGe U x u (bndB u g) (C * errX s u g)

end Generic

def ell (D : D7) : ℝ := Real.log D.host.rdE + |dlogL D 1|

section Obj

open GlobalTheory.Mean4 GlobalTheory.Mean4O Formalism.BasicNotions.DV

structure HypothesesH : Prop where
  sieg : GlobalTheory.Published.SiegelToroidalIntegral
  fan : GlobalTheory.Published.ToroidalChartsForFan
  charts : GlobalTheory.Published.ToroidalCharts
  deg : GlobalTheory.Published.ArDegree

end Obj

end GlobalTheory.CovHt

end
