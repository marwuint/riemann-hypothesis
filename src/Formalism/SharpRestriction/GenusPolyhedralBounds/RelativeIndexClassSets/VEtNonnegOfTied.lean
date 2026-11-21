import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LenAtEqZeroOfSubsingleton

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

def vEt (Q : LocalPointData G la) (ζ : PtsG G la) : ℝ :=
  if j < D.R.m then (X.vAt la (Q.y ζ) (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ)) else 0

theorem ep_nu_int {S : Scal B} (Q : LocalPointData G la) (hTie : Q.InTie S) (ζ : PtsG G la) :
    ∃ n : ℤ, (ep (unifO X la G.N) ζ : ℝ) * Q.nu S ζ = n := (hTie ζ).2.2.2.1

theorem levels_eq [Fintype (PtsG G la)] (Q : LocalPointData G la) (T : ℕ) (c : ℝ) :
    (T : ℝ) * max 0 c * ∑ ζ, ((ep (unifO X la G.N) ζ : ℝ) * (fdeg ζ : ℝ)) * vEt Q ζ =
      if j < D.R.m then (T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))) * Q.Net else 0 := by
  split_ifs with hj
  · unfold LocalPointData.Net vEt
    rw [finsum_eq_sum_of_fintype]
    simp only [if_pos hj]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    ring
  · unfold vEt
    simp only [if_neg hj, mul_zero, Finset.sum_const_zero]

end Formalism.MainNotions.Gaps.EtaleWeightGaps
