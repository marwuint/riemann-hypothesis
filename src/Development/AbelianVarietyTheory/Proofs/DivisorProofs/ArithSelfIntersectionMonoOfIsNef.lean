import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanHeightNefOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionMonoOfHeightNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleIsNefTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNefMono

theorem selfInter_mono_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), A.IsNef D → B.IsNef D → Le B A → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  intro hc hA hS k _ X _ p D hv A B α β hAn hBn hle hα hβ
  refine _root_.GlobalTheory.HSNef.selfInter_mono hc k X p D hv A B α β hle (fun x y => ?_) hα hβ
  exact _root_.GlobalTheory.KleimanNef.htNef_of_isNef hc hA hS k X p D hv _
    (_root_.GlobalTheory.NefTens.isNef_tens hc k X p D hv _ _ (GlobalTheory.NefPow.isNef_pow hc k X p D hv A x hAn)
      (GlobalTheory.NefPow.isNef_pow hc k X p D hv B y hBn))

end GlobalTheory.HSNefMono
