import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapDomainFstEqOfCoeffMatrixFamilyBilateralSubstiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCoStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionCompEqMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionScalarMonomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitaryRealPointsOfGramEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseUnitaryRealPointsAlgebraicEntries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomWeilActionFockPureTensorSubstituti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanCharacterTheta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAvg

open MvPolynomial

variable {D : D7}

theorem substMat_mul (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (g₁ g₂ : GA D V) :
    substMat θ V m d (g₁ * g₂) = substMat θ V m d g₁ * substMat θ V m d g₂ := by
  ext k' k
  simp only [substMat, Matrix.mul_apply]
  have e : (fun τ => compAt θ τ (Formalism.L2.Theta.mt V (g₁ * g₂))) =
      (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₁)) * (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₂)) :=
    funext fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_mul θ τ V g₁ g₂
  have e1 : (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)) = (fun _ => 1) * (fun _ => 1) := by
    funext τ; simp
  have e2 : GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
      (fun τ => compAt θ τ (Formalism.L2.Theta.mt V (g₁ * g₂))) (monomial k.1 1) =
      GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
        (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₁))
        (GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
          (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₂)) (monomial k.1 1)) := by
    rw [_root_.GlobalTheory.CompactHowe.substF_mul, ← e, ← e1]
  rw [e2]
  conv_lhs => rw [eq_sum_mon (d := d) (GlobalTheory.CompactHowe.substF _ _ (monomial k.1 1))
    (fun k'' h => (GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero _ _ _ _ h).trans k.2)]
  rw [map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun k'' _ => ?_
  rw [map_smul, coeff_smul, smul_eq_mul, mul_comm]

theorem substMat_cont {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ)
    (k' k : Mon D m V.rank d) :
    Continuous (fun g : GinfC V => substMat θ V m d g.1 k' k) := by
  have hc := (GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic (ι := D.what₂.Tau) (N := m) (n := V.rank) k.1 k'.1).1
  have hm : Continuous fun g : GinfC V => (fun τ : D.what₂.Tau => compAt θ τ (Formalism.L2.Theta.mt V g.1)) :=
    continuous_pi fun τ =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp ((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_subtype_val)
  have hp : Continuous fun g : GinfC V => ((fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)),
      (fun τ : D.what₂.Tau => compAt θ τ (Formalism.L2.Theta.mt V g.1))) := continuous_const.prodMk hm
  have := hc.comp hp
  exact this

theorem substMat_alg (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ)
    (k' k : Mon D m V.rank d) (g : GA D V) (hg : ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g) a b)) :
    IsAlgebraic ℚ (substMat θ V m d g k' k) := by
  have ha := (GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic (ι := D.what₂.Tau) (N := m) (n := V.rank) k.1 k'.1).2
    (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) (one_alg m) hg
  exact ha

theorem substMat_central (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (z : GA D V) (τ₀ : D.what₂.Tau) (ζ : ℂ)
    (h1 : compAt θ τ₀ (Formalism.L2.Theta.mt V z) = ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (h2 : ∀ ρ, ρ ≠ τ₀ → compAt θ ρ (Formalism.L2.Theta.mt V z) = 1) :
    substMat θ V m d z = (ζ ^ d τ₀) • (1 : Matrix (Mon D m V.rank d) (Mon D m V.rank d) ℂ) := by
  classical
  have e : (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt V z)) =
      fun ρ => if ρ = τ₀ then ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1 := by
    funext ρ
    by_cases hρ : ρ = τ₀
    · subst hρ; rw [if_pos rfl, h1]
    · rw [if_neg hρ, h2 ρ hρ]
  ext k' k
  simp only [substMat, e, _root_.GlobalTheory.CompactHowe.substF_scalar_monomial, coeff_smul, coeff_monomial, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rw [show Finsupp.mapDomain Prod.fst k.1 = d from k.2]
  by_cases h : k' = k
  · subst h; simp
  · have h' : (k.1 : FVar D m V.rank →₀ ℕ) ≠ k'.1 := fun e => h (Subtype.ext e.symm)
    simp [h, h']

end GlobalTheory.RealAvg

namespace GlobalTheory.RealAvg

end GlobalTheory.RealAvg
