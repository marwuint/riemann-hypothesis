import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDrop
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.APrime
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Proportional
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerArithAgreementStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerGeometricAgreement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreePolynomialEval
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPolynomialEval

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem eval_formPoly_none_zero {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → Option σ) → ℝ) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) (PB.formPoly n a) =
      eval c (PB.formPoly n fun w => a fun j => some (w j)) := by
  have h : ∀ Q : MvPolynomial (Option σ) ℝ,
      eval c (aeval (fun o : Option σ => o.elim (0 : MvPolynomial σ ℝ) X) Q) =
        eval (fun o : Option σ => o.elim 0 c) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p o hp =>
      rw [map_mul, map_mul, map_mul, hp]
      cases o <;> simp
  rw [← h, PB.killNone_formPoly]

theorem linA_zero_pow {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (k : ℕ) :
    linA lam 0 ^ k = toA (linRoot lam ^ k) := by
  simp [linA, toA, map_pow]

theorem swapWt_uncurry {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a b : Fin N) (lam : Wt Ψ N) :
    (fun x : Ψ × Fin N => swapWt τ a b lam x.1 x.2) =
      (fun x : Ψ × Fin N => lam x.1 x.2) ∘ Equiv.swap (τ, a) (τ, b) := by
  funext ⟨σ, i⟩
  by_cases hσ : σ = τ
  · subst hσ
    by_cases h1 : i = a
    · subst h1; simp [swapWt]
    · by_cases h2 : i = b
      · subst h2; simp [swapWt]
      · simp [swapWt, Equiv.swap_apply_def, h1, h2]
  · simp [swapWt, Equiv.swap_apply_def, hσ]

theorem eval_rho_antisymDelta_ne {Ψ : Type} [Fintype Ψ] {N : ℕ} :
    eval (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) ≠ 0 := by
  simp only [GroundTheory.Heights₂.Heights.antisymDelta, map_prod, map_sub, eval_X]
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun a _ =>
    Finset.prod_ne_zero_iff.2 fun b hb => ?_
  have hab : a < b := Finset.mem_Ioi.1 hb
  have hab' : (a : ℕ) < b := hab
  have : ((a : ℕ) : ℝ) < b := by exact_mod_cast hab'
  simp only [rhoWt]
  intro h
  linarith

end GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem Realis_PB_gapS_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {D : ℕ} {σ : Type} [Fintype σ]
    {S : PB.AnSys D (Option σ)} {P : Ideal (MRing ι)} (Re : PB.Realis S P) (II : IntersectionSystem) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) (Re.PB II) = eval c ((Re.comap some).PB II) :=
  eval_formPoly_none_zero _ _ c

theorem AnSys_degPoly_gapS_zero {D : ℕ} {σ : Type} [Fintype σ] (S : PB.AnSys D (Option σ)) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) S.degPoly = eval c (S.comap some).degPoly :=
  eval_formPoly_none_zero _ _ c

end GlobalTheory.CompanionTheory.Ar.Top
