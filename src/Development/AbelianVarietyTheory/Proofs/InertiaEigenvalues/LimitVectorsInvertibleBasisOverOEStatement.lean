import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitVectorsInvertibleBasisOverOE
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatPowDvdPerPowMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPoles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPoles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverse

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitVectors_invertible_basis_over_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)), (∀ n, ∃ R' : Matrix (Fin (d' n)) (Fin d) (WCb l), (∀ i j, R' i j ∈ bk.OE) ∧ ∀ i j, (l : WCb l) ^ n ∣ (R n * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ n i j, R n i j ∈ bk.OE) → ∃ V V' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, V i j ∈ bk.OE) ∧ (∀ i j, V' i j ∈ bk.OE) ∧ V * V' = 1 ∧ ∀ j k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ ((fun i => V i j) - R k *ᵥ fun a => bk.evW (s' a)) i := by
  first | (exact @GlobalTheory.LimVec.invertible_basis) | (exact GlobalTheory.LimVec.invertible_basis) | (intros; apply GlobalTheory.LimVec.invertible_basis  <;> assumption)
