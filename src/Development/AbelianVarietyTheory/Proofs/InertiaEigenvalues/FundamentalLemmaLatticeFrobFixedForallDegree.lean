import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetResMat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRestrictionLatticeColumn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBdRPlusUnitMatrixRestrictionLatticeMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionLatticeColumnsConditionLinearIndepend
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRestrictionLatticeColumnsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobFixedLatticeConditionSmulOfFrobeniusFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedUnramifiedTowerBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedMatrixUnitsOfLatticeBasis

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem flAt_all : ∀ r : ℕ, FLAt r := by
  intro r l _ P AI T n _ _ U x y hxy hU hc
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact x.1.elim0
  obtain ⟨E, ω, -, -, -, hω, hlin, hspan, hdet⟩ := _root_.GlobalTheory.PMon.UnrDeg.fixed_field_deg l r hr
  have hdet' : (frobMat ω).det ≠ 0 := hdet
  have hxy' : ((0 : Fin 1), ((x.2, x.1) : n × Fin r)) ≠ (0, (y.2, y.1)) := by
    intro h
    apply hxy
    simp only [Prod.mk.injEq, true_and] at h
    exact Prod.ext h.2 h.1
  obtain ⟨A₀, hA₀, hW⟩ := _root_.GlobalTheory.PMon.FLOne.flAt_one l P AI T (n × Fin r) (fun _ => U0 P ω hdet' U) _ _ hxy'
    (fun _ => GlobalTheory.T.isBdRPlusUnitMatrix_restrictionLatticeMatrix l P r ω hdet' n U hU) (_root_.GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil l P r ω hω hdet' n U x hc)
  obtain ⟨W₀, hW₀, heq⟩ := hW 0
  have he : ∀ j : n × Fin r, eps ((0 : Fin 1), ((x.2, x.1) : n × Fin r)) (0, (y.2, y.1)) (0, j) = eps x y (j.2, j.1) := by
    intro j
    simp only [eps, Prod.mk.injEq, true_and, Prod.ext_iff]
    grind
  have heq' : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet' U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    simpa [he] using heq
  have hA₀' : ∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j :=
    fun i j => by simpa using hA₀ i j
  have h3 := _root_.GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent l P r ω hω hdet' n U x y A₀ hA₀' W₀ hW₀ heq'
  obtain ⟨a, -, -, hsp⟩ := _root_.GlobalTheory.exists_frFixed_tower_basis l r ω hω hlin hspan (n → P.R.B) n (colv P ω A₀) h3.2
    (fun e he c => GlobalTheory.T.mem_span_restrictionLattice_columns l P r hr ω hω hdet' n U x y A₀ hA₀' W₀ hW₀ heq' _ (_root_.GlobalTheory.PMon.ResR.latC_smul_of_fr_fixed l P r n U x y _ e he (h3.1 c)))
  exact _root_.GlobalTheory.PMon.Extract.extract l P r ω hω hdet' n U x y hU A₀ hA₀' W₀ hW₀ heq' a hsp

end GlobalTheory.PMon

end
