import Mathlib
import Formalism.HermitianCurvature.StatementTB

namespace Formalism.FourierDecayAlt.crystallineComparison

open MeasureTheory Filter Topology Finset

noncomputable section

open Classical

abbrev V (f : ℕ) := Fin f → ℂ

def mfac (K : ℕ) (L a : ℝ) : ℝ := if a = 0 then 1 else min 1 ((L / a) ^ K)

def mL {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (σ : V f) : ℝ := ∏ v, mfac K (L v) ‖σ v‖

def pat {f : ℕ} (L : Fin f → ℝ) (σ : V f) : Finset (Fin f) := univ.filter (fun v => L v < ‖σ v‖)

def psi {f : ℕ} (z : V f) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (z v + starRingEnd ℂ (z v)))

def dualSet {f : ℕ} (La : Submodule ℤ (V f)) : Set (V f) := {σ | ∀ z ∈ La, psi (σ * z) = 1}

def fourier {f : ℕ} (g : V f → ℝ) (σ : V f) : ℂ := ∫ z, (g z : ℂ) * psi (σ * z)

def PDOn {f : ℕ} (T : Set (V f)) (A : V f → ℂ) : Prop :=
  ∀ (S : Finset (V f)) (c : V f → ℂ), (∀ σ ∈ S, σ ∈ T) →
    0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re

def Bdd {α : Type} (g : α → ℂ) : Prop := ∃ B : ℝ, ∀ x, ‖g x‖ ≤ B

def IsMean {Λ : Type} [AddCommGroup Λ] (LIM : (Λ → ℂ) → ℂ) : Prop :=
  (∀ g h, Bdd g → Bdd h → LIM (g + h) = LIM g + LIM h) ∧
  (∀ (c : ℂ) g, Bdd g → LIM (c • g) = c * LIM g) ∧
  (∀ g, Bdd g → (∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) → 0 ≤ (LIM g).re ∧ (LIM g).im = 0) ∧
  LIM (fun _ => 1) = 1 ∧
  (∀ g (σ : Λ), Bdd g → LIM (fun x => g (x + σ)) = LIM g)

def atInfAll (f : ℕ) : Filter (V f) :=
  ⨅ v : Fin f, Filter.comap (fun x : V f => ‖x v‖) Filter.atTop

def IsMeanInf {f : ℕ} (Λ : AddSubgroup (V f)) (LIM : (Λ → ℂ) → ℂ) : Prop :=
  IsMean LIM ∧ ∀ g : Λ → ℂ, Bdd g →
    Tendsto g (Filter.comap (fun x : Λ => (x : V f)) (atInfAll f)) (𝓝 0) → LIM g = 0

def MajIntegral : Prop :=
  ∀ (K : ℕ) (x : ℝ), 2 < K → 0 < x →
    Integrable (fun l : ℂ => mfac K x ‖l‖) ∧
      ∫ l : ℂ, mfac K x ‖l‖ = Real.pi * x ^ 2 * K / ((K : ℝ) - 2)

def MajIntegralProd : Prop :=
  ∀ (f K : ℕ) (x : Fin f → ℝ), 2 < K → (∀ v, 0 < x v) →
    Integrable (fun l : V f => mL K x l) ∧
      ∫ l : V f, mL K x l = ∏ v, (Real.pi * x v ^ 2 * K / ((K : ℝ) - 2))

def MeanBound : Prop :=
  ∀ (Λ : Type) [AddCommGroup Λ] (LIM : (Λ → ℂ) → ℂ) (g : Λ → ℂ) (B : ℝ),
    IsMean LIM → (∀ x, ‖g x‖ ≤ B) → ‖LIM g‖ ≤ B

def MeanExists : Prop :=
  ∀ (f : ℕ) (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La],
    ∃ LIM : (La.toAddSubgroup → ℂ) → ℂ, IsMeanInf La.toAddSubgroup LIM

def MeanSplit : Prop :=
  ∀ (f : ℕ) (Λ : AddSubgroup (V f)) (LIM : (Λ → ℂ) → ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (a r : V f → H) (Nh : V f → ℂ) (B : ℝ),
    IsMeanInf Λ LIM → (∀ x, ‖a x‖ ≤ B ∧ ‖r x‖ ≤ B) →
    (∀ σ ∈ Λ, Tendsto (fun x => inner ℂ (a x) (a (x + σ))) (atInfAll f) (𝓝 (Nh σ))) →
    (∀ σ ∈ Λ, Tendsto (fun x => inner ℂ (a x) (r (x + σ))) (atInfAll f) (𝓝 0)) →
    (∀ σ ∈ Λ, Tendsto (fun x => inner ℂ (r x) (a (x + σ))) (atInfAll f) (𝓝 0)) →
    (∀ σ ∈ Λ, LIM (fun x : Λ => inner ℂ (a x + r x) (a ((x : V f) + σ) + r ((x : V f) + σ))) =
        Nh σ + LIM (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ)))) ∧
    PDOn (Λ : Set (V f)) (fun σ => LIM (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ))))

def LatticeHerglotzBound : Prop :=
  ∀ (f : ℕ) (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (N : V f → ℝ) (A : V f → ℂ),
    (∀ z, 0 ≤ N z) → LowerSemicontinuous N → Integrable N → PDOn (dualSet La) A →
    Summable (fun σ : dualSet La => ‖fourier N σ + A σ‖) →
    ∀ (z₀ : V f) (S : Finset (V f)), (∀ z ∈ S, z - z₀ ∈ La) →
      ZLattice.covolume La * ∑ z ∈ S, N z ≤ ∑' σ : dualSet La, ‖fourier N σ + A (σ : V f)‖

def SumForm {E W : Type} [Field E] (D : TB.Data E W) (ε : ℝ) (i s : ℕ) (w : W) (Mv : ℝ) : Prop :=
  ∃ θ : W → ℝ, TB.IsProb (D.Wb (D.cnt w + s * D.K)) θ ∧
    ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - s) → ∀ κ, TB.PSDOn Y κ →
      ∀ (t₀ : E) (S : Finset E), (∀ t ∈ S, t ≠ 0 ∧ t - t₀ ∈ D.La (i - s + 1) s) →
        ∑ t ∈ S, (D.Nst ε i s w Y κ t t).re ≤
          Mv * ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * D.N0 ε (i - s) w' Y κ

def EstBlockOfSumForm : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (C₄ : ℝ), D.GramPSD → D.WordsPos →
    (∀ ε, 0 < ε → ∀ i s, 2 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ w ∈ D.Wall,
      D.cnt w + (s + 1) * D.K ≤ D.Ntop → D.vol (i - s + 1) s ≤ 1 →
      ∃ Mv, Mv ≤ C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') ∧ SumForm D ε i s w Mv) →
    D.EstBlock C₄

end

end Formalism.FourierDecayAlt.crystallineComparison
