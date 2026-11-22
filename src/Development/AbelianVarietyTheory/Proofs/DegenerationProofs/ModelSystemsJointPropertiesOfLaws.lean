import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelUniformisationOfAbelianLocusDirectImage
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcFamilyFourthConditionInvertiblePushforward
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN

theorem partI_of_inputs : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ModelsSt → N0 → PartI := by
  intro hT h1 h2 h3 h4 h5 h6 hE hU hP hH hA hM h0
  refine ⟨h0, fun E _ _ _ H D hD Xo => ?_⟩
  obtain ⟨Y, hY, hgl⟩ := hM E H D hD Xo
  refine ⟨Y, fun p W hp hW => ⟨(hY p W hp hW).1, fun i => ⟨((hY p W hp hW).2 i).1, ?_, ?_⟩⟩, hgl⟩
  · exact _root_.GlobalTheory.model_uniformisation_of_clauses h1 h2 h3 h4 h5 hE hU hP E H D _ _ _ _ _ p ((hY p W hp hW).1.1 i)
  · exact _root_.GlobalTheory.LN.ArcClause.arc_clause hT h1 h2 h3 h4 h5 h6 hE hU hP hH hA E H D _ _ _ _ _ p ((hY p W hp hW).1.1 i)
      ((hY p W hp hW).2 i).2

end GlobalTheory.LN
