import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.IsHypPair
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.RenameBlockSingleVariableSeries
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS phFF NormRel)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog at1 lgF)

namespace GlobalTheory.KerStd

def CurveData (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) : Prop :=
  5 ≤ l ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧
    UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsLawOfLog l F ∧
    ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α

def HostLog (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n] (Θ : MvPowerSeries n ℂ_[l]) : Prop :=
  Formalism.DworkPowerSeriesWeights.Integral
    (Formalism.DworkPowerSeriesWeights.mvExp (∑ i : n, at1 i (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) : MvPowerSeries n ℂ_[l]) *
      (MvPowerSeries.subst (fun i : n => (at1 i (lgF ℂ_[l] l) : MvPowerSeries n ℂ_[l])) Θ : MvPowerSeries n ℂ_[l]))

abbrev HypPair {K : Type} [NormedField K] (σ : K →+* K) {E n : Type} [DecidableEq E] [Fintype n] (f f' : E → n → K) : Prop :=
  Formalism.L2.Th1.Top.IsHypPair σ f f'

def thOrth (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (F₀ : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N =>
    ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * MvPowerSeries.X i) F₀

def HostAt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime]
    (lam : Qbar →+* ℂ_[p]) : Prop :=
  ∃ (c : ℂ_[p]) (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)),
    ‖c‖ = 1 ∧ CurveData p g2 g3 s2 ε σ F ∧
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        LocBasis D p (YYl D L L') b ∧ TaylorLogMetric.Orthonormal D b ∧
        ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → HostLog p g2 g3 s2 ε (thOrth D lam c b G)

theorem HypPair.symm {K : Type} [NormedField K] {σ : K →+* K} {E n : Type} [DecidableEq E] [Fintype n] {f f' : E → n → K}
    (h : HypPair σ f f') : HypPair σ f' f := by
  obtain ⟨a, b, c, d, e⟩ := h
  refine ⟨b, a, d, c, fun x y => ?_⟩
  have := congrArg σ (e y x)
  rw [map_sum] at this
  simp only [map_mul, (a _ _).2] at this
  rw [show (∑ i, σ (f' x i) * f y i) = ∑ i, f y i * σ (f' x i) from Finset.sum_congr rfl fun i _ => mul_comm _ _, this]
  by_cases hxy : x = y
  · subst hxy; simp
  · have h' : ¬ y = x := fun q => hxy q.symm
    simp [hxy, h']

theorem HostLog.iff_phSum (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n] (Θ : MvPowerSeries n ℂ_[l]) :
    HostLog l g2 g3 s2 ε Θ ↔ Formalism.DworkPowerSeriesWeights.Integral
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (Formalism.L2.Th1.Top.phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) *
        (MvPowerSeries.subst (fun i : n => (at1 i (lgF ℂ_[l] l) : MvPowerSeries n ℂ_[l])) Θ : MvPowerSeries n ℂ_[l])) :=
  Iff.rfl

theorem HostLog.constantCoeff_subst {K σ τ : Type} [Field K] [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f : MvPowerSeries τ K) = MvPowerSeries.constantCoeff f := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have e : f = (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) + MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by ring
  conv_lhs => rw [e]
  rw [MvPowerSeries.subst_add hs, map_add, MvPowerSeries.constantCoeff_subst_eq_zero hs ha (by simp), zero_add,
    MvPowerSeries.subst_C]
  simp

end GlobalTheory.KerStd
