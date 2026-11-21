import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.HermitianLattices.StatementMass
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.SArith
import Formalism.SharpRestriction.CuspSpanNormBounds.DstarEq
import Formalism.SharpRestriction.ParConsts

noncomputable section

namespace Formalism.MainNotions.PlaceDegreeData

open MeasureTheory NumberField Matrix Finset IsDedekindDomain
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S

def qOf {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter fun a => ε a = false).card

def pOf {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter fun a => ε a = true).card

def decBound {n : ℕ} (q : ℕ) (h : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.exp (-(h / 8) * min (Formalism.REAL.hs X) (Real.sqrt (Formalism.REAL.hs X) / Real.sqrt (2 * (q : ℝ))))

def phLoc {n : ℕ} (ε : Fin n → Bool) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Formalism.REAL.UJ ε → ℂ :=
  fun g => ((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star (coefOn σ w w g)

def phe (I : AutInst) (ph : I.Ginf → ℂ) (e : I.Gf → ℂ) : I.GA → ℂ := fun x => ph x.1 * e x.2

def fdegAll (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (w : ∀ v, H v) : ℝ :=
  ∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)

def phOf (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (w : ∀ v, H v) : I.Ginf → ℂ :=
  fun g => ((fdegAll I σ w : ℝ) : ℂ) * star (∏ v, coefOn (σ v) (w v) (w v) (g v))

def HidaSetting (I : AutInst) (n₀ : ℕ) (A b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (μf : Measure I.Gf) (g g₀ : ℕ) (e : I.Gf → ℂ) : Prop :=
  n₀ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧
    Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧
    I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ SplitsCompl I.E g₀

def q0At (I : AutInst) (v : InfinitePlace I.F) : ℕ := min (I.pAt v) (I.qAt v)

def CountData (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs))
    (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (e : I.Gf → ℂ)
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) : Prop :=
  (∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧
    I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧
    I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re

def phA {G : Type*} [Group G] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (d : ℝ)
    (σ : G →* (H →L[ℂ] H)) (w : H) : G → ℂ :=
  fun g => (d : ℂ) * star ⟪w, σ g w⟫_ℂ

def IsOpIntA {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) {Hp : Type*} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (φ : G → ℂ) (P : Hp →L[ℂ] Hp) : Prop :=
  Integrable φ μ ∧ ∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ

def PointsLemma (_D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h →
    Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) →
    Real.log (Real.log b) ≤ cb * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) →
    |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (fdegAll I σ w) μf fund e| ≤
      Real.exp (-c * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (fdegAll I σ w) μf fund e

def RowsTie (D : Formalism.BasicNotions.D7) (X : RowsAut) : Prop :=
  (∃ pl : InfinitePlace X.I.F ≃ D.what₂.Tau, AutTie D X pl) ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (X.lam v)) ∧
    (SplitsCompl D.host.E (D.host.g 0) → SplitsCompl X.I.E X.g₀)

end Formalism.MainNotions.PlaceDegreeData
