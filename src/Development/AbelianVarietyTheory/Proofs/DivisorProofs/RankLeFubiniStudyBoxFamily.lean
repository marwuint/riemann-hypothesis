import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyBundleIsNefOfNonnegWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFubiniStudyRatFnsMemPairSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeGeometricDegreeOfIsNef
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem fs_box_rank_le : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J]
    (e : J → X.functionField) (x : Fin D → X.functionField) (w : J × Finset (Fin D) → ℝ),
    LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, 0 ≤ w c) →
    IsFS M (boxFam e x) w → (D.factorial : ℝ) * Fintype.card J ≤ gdeg M D := by
  intro hAr hHS k _ X _ p D hD M J _ e x w he hx hw hFS
  have hNef : M.IsNef D := _root_.GlobalTheory.HSNef.FSNef.isNef_of_isFS hAr k X p D hD M _ (boxFam e x) w hFS hw
  obtain ⟨P, hPL, hmem⟩ := _root_.GlobalTheory.HSNef.isFS_mem_pair k X p M _ (boxFam e x) w hFS
  subst hPL
  exact _root_.GlobalTheory.HSNef.RankNef.rank_le_gdeg_of_isNef hAr hHS k X p D hD P hNef J e x he hx hmem

end GlobalTheory.HSNef
