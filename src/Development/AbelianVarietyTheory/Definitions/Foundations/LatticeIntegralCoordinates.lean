import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric

noncomputable section

namespace GlobalTheory.Glob.IntegralWittCoefficients

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions.TaylorLogMetric

def Wp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  (Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}).topologicalClosure

def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])

def tauK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : D.host.K) : ℂ_[p] :=
  lamC lam (D.host.φ₀ (a : D.host.E))

def hP {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] (x y : ι → ℂ_[p] × ℂ_[p]) : ℂ_[p] × ℂ_[p] :=
  ∑ k, x k * (y k).swap

def IsModelU {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : Prop :=
  let W := C • wModel lam Λ
  IsIntP W.a₁ ∧ IsIntP W.a₂ ∧ IsIntP W.a₃ ∧ IsIntP W.a₄ ∧ IsIntP W.a₆ ∧ ‖W.Δ‖ = 1

structure G1 (p : ℕ) [Fact p.Prime] where
  lam : Qbar →+* ℂ_[p]
  abelian₂ : AddSubgroup ℂ
  C : WeierstrassCurve.VariableChange ℂ_[p]
  wq : PowerSeries ℂ_[p]
  ex : PowerSeries ℂ_[p]

namespace G1

variable {p : ℕ} [Fact p.Prime] (g : G1 p)

def W : WeierstrassCurve ℂ_[p] := g.C • wModel g.lam g.abelian₂

def l : PowerSeries ℂ_[p] := flog g.W g.wq

def Ok : Prop :=
  IsModelU g.lam g.abelian₂ g.C ∧ IsWq g.W g.wq ∧
    PowerSeries.constantCoeff g.ex = 0 ∧ PowerSeries.subst g.ex g.l = PowerSeries.X

def ph : PowerSeries ℂ_[p] := -logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)

variable {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a g.l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x g.ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := g.pt (g.lg a + g.lg b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := g.pt (g.lg a - g.lg b)

def mulBy (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  g.pt (MvPowerSeries.C c * g.lg a)

def lin {ι : Type*} [Fintype ι] (c : ι → ℂ_[p]) (a : ι → MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  g.pt (∑ j, MvPowerSeries.C (c j) * g.lg (a j))

def phAt (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a g.ph

def be (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  g.phAt (g.add a b) - g.phAt a - g.phAt b

end G1

def At (D : D7) {p : ℕ} [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p) : Prop :=
  IsCurveIdeal D cc ∧ Nat.Coprime (Ideal.absNorm cc) p ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧
    g.abelian₂ = lamOf D cc δ ∧ g.Ok

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

def ser1 {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (G : ℂ → ℂ) : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => lamC lam (iteratedDeriv n G 0 / (n.factorial : ℂ))

def G1.atU {p : ℕ} [Fact p.Prime] (g : G1 p) (G : ℂ → ℂ) : PowerSeries ℂ_[p] :=
  PowerSeries.subst (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * g.l)
    (ser1 g.lam G)

def IsTwoTorsionPointUnkilled (D : D7) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ ∧
    ((1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ

def th0 (Λ : AddSubgroup ℂ) (t0 : ℂ) : ℂ → ℂ :=
  fun z => U1 Λ t0 (sgStar Λ) z / U1 Λ t0 (sgStar Λ) 0

def G1.jetPh {p : ℕ} [Fact p.Prime] (g : G1 p) (i : ℕ) : ℂ_[p] :=
  (i.factorial : ℂ_[p]) * PowerSeries.coeff i (PowerSeries.subst g.ex g.ph : PowerSeries ℂ_[p])

def G1.PhOn {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι : Type*} [Fintype κ] [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries ι ℂ_[p] :=
  ∑ k, g.phAt (g.lin (fun e => (b e k).1) (fun e => Xv e))

def rhoOf (D : D7) (mt : ℕ → D.Dt →* ℂˣ) (i : ℕ) : D.Dt →* ℂˣ :=
  (mt (i + 1))⁻¹ * D.chiD ^ (-(((D.R.N (i + 1)) / 2 : ℕ) : ℤ))

def rhoOf' (D : D7) (mt : ℕ → D.Dt →* ℂˣ) (i : ℕ) : D.Dt →* ℂˣ :=
  mt (i + 1) * D.chiD ^ ((((D.R.N i) / 2 : ℕ) : ℤ))

def CarriesTupleCharacters (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ)
    (dt : ∀ i, C.cls i → D.Dt) : Prop :=
  ∀ i < D.R.m, (∀ c, C.rhoDet i c = ((rhoOf D mt i (dt i c) : ℂˣ) : ℂ)) ∧
    ∀ c, C.rhoDet' i c = ((rhoOf' D mt i (dt (i + 1) c) : ℂˣ) : ℂ)

structure LiftObj (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) where
  mt : ℕ → D.Dt →* ℂˣ
  L0 : ∀ i, (letI := D.host.cmStar; SDLat D.host.E (D.R.N i))
  lattice_integral_coordinates : ∀ i (x : Fin (D.R.N i) → D.host.E), x ∈ (L0 i).1 ↔ ∀ k, IsIntegral ℤ (x k)
  lat : ∀ i, C.cls i → (letI := D.host.cmStar; SDLat D.host.E (D.R.N i))
  dt : ∀ i, C.cls i → D.Dt
  dt_lat : ∀ i c, (QuotientGroup.mk (dt i c) : D.Dt ⧸ D.UO) = D.relDet (D.R.N i) (L0 i) (lat i c)
  c13 : CarriesTupleCharacters D C mt dt
  frm : ∀ i, C.Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ
  frm_inj : ∀ i ≤ D.R.m, Function.Injective (frm i)
  frm_range : ∀ i ≤ D.R.m, ∀ f : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ,
    (∃ y, frm i y = f) ↔ ∀ τ, (f τ).det ≠ 0
  frm_de : ∀ i ≤ D.R.m, ∀ y τ, C.de i y τ = (frm i y τ).det
  dgen : D.what₂.Tau → ℂ
  dgen_gen : ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), (∀ τ x, embT D τ x ∈ M) ∧ ∀ τ, ∃ s : M, (s : ℂ) = dgen τ ∧
    ellT D M τ = Submodule.span (𝓞 M) {s}
  S : Finset ℕ
  Th : ∀ i, C.cls i → C.cls (i + 1) → VC D (D.R.N i) (D.R.N (i + 1)) → ℂ

def hf1 (Λ : AddSubgroup ℂ) (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w / (area Λ : ℂ)

def normSq1 (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : ℝ :=
  let Fd : Set ℂ := Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (hf1 Λ z z).re)

end GlobalTheory.Glob.IntegralWittCoefficients
