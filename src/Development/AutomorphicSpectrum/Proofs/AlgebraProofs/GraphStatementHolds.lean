import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphIdealArithmeticVarietyImage
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphIdealFibreChartDegree
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem graphStatement : GraphStatement := by
  intro K _ ι _ K₂ _ ι₂ _ P d g δ hP hg hne
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Giv.graphIdeal_isArithVar K ι K₂ ι₂ P d g δ hP hg hne
  refine ⟨h1, h2, ?_⟩
  intro G J hJ
  have hP' : IsArithVar (imageZ inlV (graphIdeal P g)) d := by rw [h2]; exact hP
  have hF : IsProjVarF (fibreIdeal Sum.inl G) 0 :=
    GlobalTheory.CompanionTheory.Ar.Giv.fibreDim K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV (graphIdeal P g) d 0 G
      isBlockMap_inl h1 hP'
  have hrel := hF.1.2.2
  let i : ∀ k, fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂) k := fun k => (hrel k).choose
  have hi : IsChart (fibreIdeal Sum.inl G) i := fun k => (hrel k).choose_spec
  rw [hJ.1 _ _ i hF hi]
  exact_mod_cast _root_.GlobalTheory.CompanionTheory.Ar.Giv.GrDeg.graph_generic_fibre_ptDeg K ι K₂ ι₂ P g hP.2.1.1 hne h2 G i hi

end GlobalTheory.CompanionTheory.Ar.Giv
