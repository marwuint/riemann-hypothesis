import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSecond
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartThird
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFourth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSixth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSeventh
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreTwistedResolution
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (cst : ℝ), IsNormFn M τ a k₀ ca cb RW (fun x => logNormSec L' v x + cst) → ∀ (U : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) → (∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)) → ∃ α : ℕ → Ψ × Fin N → (Fin d → ℂ) → ℝ, (∀ m, ∀ w ∈ U m, (G m w).PosDef) ∧ (∀ m r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G m w r s) (U m)) ∧ (∀ m p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (α m p) (U m)) ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = xiPot (G m (Fin.tail z')) (z' 0) + (Hh z').re) ∧ (∀ m p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = α m p (Fin.tail z') + (Hh z').re) ∧ ∀ m (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U m → z 0 ≠ z 1 → logNormSec L' v (ΦW m z) + cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦW m z)) + (FA.S.comap some).ph p (q 1 (ΦW m z))) = logSin (G m (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hcase hblk hca hcb RW q hq h0 h1 L' v cst hnorm U G ΦY ΦW hU hC
  have hC' := fun m => (isFibreChart_iff FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)).1 (hC m)
  choose l H bp hD using hC'
  refine ⟨fun m => alphaOf BM (l m) (H m) (bp m), fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.gramPlane_posDef K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_plane K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_alphaOf K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_xi_potential K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_base_member K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb k₀ hblk RW q h0 h1 _ hnorm (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
