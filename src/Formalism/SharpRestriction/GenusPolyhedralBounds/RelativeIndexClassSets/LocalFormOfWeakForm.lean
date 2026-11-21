import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.QlenEqZeroOfLe
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SUnitsEulerDifference
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem phiC_nonneg (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    0 ≤ X.phiC la y := by
  unfold PJ.phiC
  split_ifs with h
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    unfold ModuliIntegralCharts.Loc.phiCy ModuliIntegralCharts.phiC
    refine Real.sInf_nonneg ?_
    rintro x ⟨l, -, h2, rfl⟩
    by_cases hb : (P.loc X.dat (resCh la)).beS (X.pt66 la y) = 0
    · rw [hb]; simp
    · refine (h2 _ ?_ hb).le
      intro a
      by_cases ha : a = 0
      · subst ha; simp
      · exact ((P.loc X.dat (resCh la)).be_pos (X.pt66 la y) a ha).le
  · exact le_rfl

namespace LocDat

end LocDat

end Formalism.MainNotions.Gaps.T0
