import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.MirabolicInclusion
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.Obj

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev xAt3 (F : Face3 D A3) (R : RealDat3 D A3 Ks) : ℝ := (F.fc (R.toCx3 F).zs).Z.x

end Formalism.IndefR.Obj
