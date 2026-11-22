import Formalism.SharpRestriction.GlobalSchurBounds.LinkPk
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Formalism.LocalToGlobal.HermitianColumns.StarConj
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm
import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh
import Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq
import Formalism.LocalToGlobal.GlobalTheory.PowFourLtCeilThresholdPrime
import Formalism.LocalToGlobal.GlobalTheory.PlacesP
import Formalism.LocalToGlobal.GlobalTheory.MemCompanion
import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompact
import Formalism.GL3MeanSquares.OrbitPointsDistinct
import Formalism.BehrendSets.BehrendVariance.MemWindowIff
import Formalism.BehrendSets.BehrendVariance.ProdDimVNeZero
import Formalism.GL3MeanSquares.HookFormulaTorsion.DifferentIdealConditions
import Formalism.SharpRestriction.SmoothDesignExistence.LinkGLOBALPk
import Formalism.LocalToGlobal.GlobalTheory.FamCol
import Formalism.LocalToGlobal.GlobalTheory.AnalyticConclusionOfProp25
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassItems
import Formalism.LocalToGlobal.GlobalTheory.GL5.LocalEndomorphismContinuous
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountRec
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryClassMassHermitian

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem genus_class_mass : PI.UJClassMass2.UJClassMass := _root_.unitary_class_mass_hermitian

theorem classMass_of_D7 (D : D7) : ClassMass D := class_mass_of_genus_classes genus_class_mass D

theorem volume_mass_of_genus_rank (D : D7) (n : ℕ) (hT : VolTie D) (hG : GenusMassAt D n) : volumeAtLevelZero D n :=
  volume_mass_of_class_data D n hT hG (class_number_finite_rank D n) (classMassAt_of D (classMass_of_D7 D) n)

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

end
