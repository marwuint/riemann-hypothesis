import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvIsoOfLocalTateDualityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinIsoDualLatticeOfLocalTateDualityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLocalDualityOfLocalTateDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CohomologyShapeOfTateDualityEulerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHomModuloUnramifiedShapeOfLocalDualityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedPadicDecompositionHomExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRecStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrFiniteOverPadicTopologiesExist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCohomologySevenElementaryFactsStatement

namespace GlobalTheory

theorem langRecCore_of_artinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hT : Formalism.GaloisCohomology.LocalTateDualityK)
    (hE : Formalism.GaloisCohomology.LocalEulerCharK) : ReciprocityTheory.ChartRestriction.T2.Core where
  dec := _root_.GlobalTheory.DecLocal.decEquiv
  inv := GlobalTheory.T.invIso_of_localTateDuality hT
  fin := GlobalTheory.T.finIso_dualLattice_of_localTateDuality hT
  rat := _root_.GlobalTheory.ratIso_of_localTateDuality hT
  int := GlobalTheory.T.integral_localDuality_of_localTateDuality hT
  jspan := _root_.GlobalTheory.jSpan_holds
  nat := GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist hT
  shape := GlobalTheory.T.cohomology_shape_of_tate_duality_euler hT hE
  shapeUnr := GlobalTheory.T.galoisHom_modulo_unramified_shape_of_localDuality hT hE
  unr := _root_.GlobalTheory.UnrChar.unrDec
  vhE := GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity hA
  top := _root_.GlobalTheory.PadicTop.topEx
  elem := GlobalTheory.T.local_cohomology_seven_elementary_facts

end GlobalTheory
