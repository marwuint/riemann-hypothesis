import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeadBound

open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section

variable {r : ℕ} (X : Data E r) (g : Frame X.Ψ r → ℝ)

def IsDom (la : Wt X.Ψ r) (n : ℕ) (P : Frame X.Ψ r → ℂ) : Prop :=
  X.IsBddSec la P ∧ ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C * g x ^ n

variable {X g}

theorem IsDom.add {la : Wt X.Ψ r} {n : ℕ} {P Q : Frame X.Ψ r → ℂ} (hP : IsDom X g la n P)
    (hQ : IsDom X g la n Q) : IsDom X g la n (P + Q) := by
  obtain ⟨C, hC⟩ := hP.2
  obtain ⟨C', hC'⟩ := hQ.2
  refine ⟨bdd_add X hP.1 hQ.1, C + C', fun x hx => ?_⟩
  calc X.pnorm la (P + Q) x ≤ (‖P x‖ + ‖Q x‖) * X.nfac la x :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) (nfac_nonneg X la x)
    _ = X.pnorm la P x + X.pnorm la Q x := by rw [add_mul]; rfl
    _ ≤ C * g x ^ n + C' * g x ^ n := add_le_add (hC x hx) (hC' x hx)
    _ = (C + C') * g x ^ n := by ring

theorem IsDom.smul {la : Wt X.Ψ r} {n : ℕ} {P : Frame X.Ψ r → ℂ} (a : ℂ) (hP : IsDom X g la n P) :
    IsDom X g la n (a • P) := by
  obtain ⟨C, hC⟩ := hP.2
  refine ⟨bdd_smul X a hP.1, ‖a‖ * C, fun x hx => ?_⟩
  calc X.pnorm la (a • P) x = ‖a‖ * X.pnorm la P x := by
        rw [pnorm_eq, pnorm_eq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    _ ≤ ‖a‖ * (C * g x ^ n) := mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg a)
    _ = ‖a‖ * C * g x ^ n := by ring

theorem IsDom.mul {la la' : Wt X.Ψ r} {n n' : ℕ} {P Q : Frame X.Ψ r → ℂ} (hP : IsDom X g la n P)
    (hQ : IsDom X g la' n' Q) : IsDom X g (la + la') (n + n') (P * Q) := by
  obtain ⟨C, hC⟩ := hP.2
  obtain ⟨C', hC'⟩ := hQ.2
  refine ⟨bdd_mul X hP.1 hQ.1, C * C', fun x hx => ?_⟩
  have e : X.pnorm (la + la') (P * Q) x = X.pnorm la P x * X.pnorm la' Q x := by
    rw [pnorm_eq, pnorm_eq, pnorm_eq, Pi.mul_apply, norm_mul, nfac_add X hx]
    ring
  rw [e]
  calc X.pnorm la P x * X.pnorm la' Q x ≤ (C * g x ^ n) * (C' * g x ^ n') :=
        mul_le_mul (hC x hx) (hC' x hx) (pnorm_nonneg X _ _ _)
          ((pnorm_nonneg X _ _ _).trans (hC x hx))
    _ = C * C' * g x ^ (n + n') := by ring

end

end GlobalTheory.LeadBound
