import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

open Module NumberField IsDedekindDomain
open scoped Matrix MatrixOrder ComplexOrder
open Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN

noncomputable section

namespace GlobalTheory.Proof.DualMatrixMetricMeans

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

theorem meanInf_eq [IsTotallyComplex K] (g : InfinitePlace K → ℝ) :
    meanInf K g = (1 / (nPl K : ℝ)) * ∑ v, g v := by
  have hn : (nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  unfold meanInf
  rw [Formalism.HN.twist_finrank_eq K]
  field_simp

theorem meanInf_const [IsTotallyComplex K] (c : ℝ) : meanInf K (fun _ => c) = c := by
  have hn : (nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  rw [meanInf_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change 1 / (nPl K : ℝ) * ((nPl K : ℝ) * c) = c
  field_simp

end GlobalTheory.Proof.DualMatrixMetricMeans
