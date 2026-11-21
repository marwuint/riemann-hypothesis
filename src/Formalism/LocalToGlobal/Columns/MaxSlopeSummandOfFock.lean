import Mathlib
import Formalism.LocalToGlobal.Columns.MultiFactorialEqTripleProd
import Formalism.LocalToGlobal.Columns.BrpStarLatLattice
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PExtInvMuB
import Formalism.GL3MeanSquares.ConcavityEquidistribution

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.HermitianLattices.TraceIntegrality

section Places

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [IsTotallyComplex E] [IsTotallyComplex K]

theorem mean_over_places_comap (φ : E →+* K) (G : InfinitePlace E → ℝ) :
    (1 / (nPl K : ℝ)) * ∑ v : InfinitePlace K, G (v.comap φ) = (∑ w, G w) / (nPl E : ℝ) := by
  classical
  let _ : Algebra E K := φ.toAlgebra
  have hc := Formalism.L2.Geo.ExtensionFiltration.ExtInvMu.card_fiber E K
  have hn := Formalism.L2.Geo.ExtensionFiltration.ExtInvMu.nPl_ext E K
  have hs : ∑ v : InfinitePlace K, G (v.comap φ) = (Module.finrank E K : ℝ) * ∑ w, G w := by
    rw [← Finset.sum_fiberwise Finset.univ (fun v : InfinitePlace K => v.comap φ) (fun v => G (v.comap φ)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (fun v hv => congrArg G (Finset.mem_filter.1 hv).2), Finset.sum_const, nsmul_eq_mul]
    congr 2
    convert hc w
    rfl
  have hK : (0 : ℝ) < (nPl K : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have hE : (0 : ℝ) < (nPl E : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have hn' : (nPl K : ℝ) = (Module.finrank E K : ℝ) * (nPl E : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (Module.finrank E K : ℝ) := by
    by_contra h
    have h0 : (Module.finrank E K : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [h0, zero_mul] at hn'
    exact hK.ne' hn'
  rw [hs, hn']
  field_simp

end Places

end Formalism.L2.Col
