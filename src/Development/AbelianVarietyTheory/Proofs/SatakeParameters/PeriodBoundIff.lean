import Mathlib
import Formalism.LocalRingCardinality.DataErr
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ColumnAvoidanceConditions

noncomputable section

namespace GlobalTheory.ExpAtTypePrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain

theorem col_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (a : ℂ)
    (φ : C.cls 0 → C.Y 0 → ℂ) : C.col (a • φ) = a • C.col φ := by
  unfold ColumnChain.col
  generalize R.m = n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext j
    simp only [Formalism.ThetaLiftIndependence.chainOpM, Formalism.ThetaLiftIndependence.kerOpM, ih, Pi.smul_apply, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem perCol_smul (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (a : ℂ) (φ : D.what₂.Mu u) (F : D.what₂.Amb μ) :
    D.what₂.perCol u μ (a • φ) F = a * D.what₂.perCol u μ φ F := by
  by_cases hμ : μ = D.what₂.mu0
  · subst hμ
    simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, col_smul,
      LinearMap.smul_apply, smul_eq_mul]
  · simp only [D.perCol_tie u μ hμ, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, col_smul,
      LinearMap.smul_apply, smul_eq_mul]

end GlobalTheory.ExpAtTypePrimes

end
