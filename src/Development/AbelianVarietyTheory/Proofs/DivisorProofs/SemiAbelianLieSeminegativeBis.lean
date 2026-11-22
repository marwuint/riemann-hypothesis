import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiNegativeDescendsFieldExtensionCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianLieSeminegativeOfNeron
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSheafSemiAbelianSemiNegOfIsAlgClosed

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem semiAbelianLieSeminegative : GlobalTheory.Published.SemiAbelianLieSeminegative := by
  intro k _ _ C _ hs hp hc G _ hG W r hW i hi
  obtain ⟨C', _, π, hC', hdesc⟩ := _root_.GlobalTheory.SemiNegFieldChange.semiNeg_descends_baseChange k C ⟨hs, hp, hc⟩ (AlgebraicClosure k)
  have : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hs hc
  refine hdesc (Lie G) ?_ W r hW i hi
  exact GlobalTheory.NeronCurve.LieDescent.semiNeg_of_iso (GlobalTheory.NeronCurve.LieDescent.lieBaseIso π G).symm
    (_root_.GlobalTheory.Nef.semiNeg_lie_of_isAlgClosed (AlgebraicClosure k) C' hC' _ (IsSemiAbelian.pullback π G hG))

end GlobalTheory.Nef
