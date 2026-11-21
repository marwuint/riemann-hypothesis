import Formalism.LatticeTheta.LatticeSummableDecay

open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma norm_exp_two_pi_I_mul (r : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
  rw [show (2 * Real.pi * Complex.I * (r : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem poissonDecay_of (hD : DualIsLattice V) (h1 : LatticeSummableDecay V)
    (h2 : Periodization V) (h3 : UnfoldCoeff V) (h4 : LatticeFourierSeries V) : PoissonDecay V := by
  intro Λ _ _ f hf b hb hfO hFO x
  obtain ⟨hdd, hdz⟩ := hD Λ
  haveI := hdd
  haveI : IsZLattice ℝ (dual Λ) := hdz

  have hphase : (fun v : V => (𝓕 f : V → ℂ) v * Complex.exp (2 * Real.pi * Complex.I * (⟪v, x⟫ : ℝ)))
      =O[cocompact V] (fun v => ‖v‖ ^ (-b)) := by
    refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun v => ?_)).trans hFO
    rw [norm_mul, norm_exp_two_pi_I_mul, mul_one, one_mul]
  have hsum := h1 (dual Λ) _ b hb hphase
  refine ⟨hsum, ?_⟩
  obtain ⟨hint, hper, hcont, hinv⟩ := h2 Λ f hf b hb hfO

  let B := Module.Free.chooseBasis ℤ Λ
  have hD' := ZLattice.isAddFundamentalDomain B (volume : Measure V)
  have hcoef : ∀ μ : dual Λ,
      ∫ y in ZSpan.fundamentalDomain (B.ofZLatticeBasis ℝ Λ), (∑' l : Λ, f ((l : V) + y)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ))) = (𝓕 f : V → ℂ) μ :=
    fun μ => h3 Λ f hint _ hD' μ μ.2
  have hFs : Summable (fun μ : dual Λ => (𝓕 f : V → ℂ) μ) := h1 (dual Λ) _ b hb hFO
  have hG := h4 Λ (fun y => ∑' l : Λ, f ((l : V) + y)) hcont
    (fun l y => by simpa using hinv l y) _ hD' (by simpa only [hcoef] using hFs) x
  simp only [hcoef] at hG
  have hval : (ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ, (𝓕 f : V → ℂ) μ *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)) = ∑' l : Λ, f ((l : V) + x) := by
    rw [← tsum_mul_left, ← hG.tsum_eq]
    congr 1; funext μ; ring
  rw [hval]
  exact (hper x).hasSum

theorem poissonSchwartz_of (hP : PoissonDecay V) (h6 : SchwartzDecay V) : PoissonSchwartz V := by
  intro Λ _ _ f x
  have hd : (Module.finrank ℝ V : ℝ) < Module.finrank ℝ V + 1 := by linarith
  exact hP Λ f f.continuous _ hd (h6 f _).1 (h6 f _).2 x

end Formalism.H
