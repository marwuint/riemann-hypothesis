import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MonomialNorms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.abelian₂
open Formalism.MainNotions Formalism.BasicNotions

variable {D : D7}

abbrev CMObj (T : Core D) (j : ℕ) : Type 1 :=
  @LamObj D.host.E _ _ _ T.Q.H.starRing T.Q.H T.Q.l T.Q.c ((T.Q.Dw j).p - 1) ((T.Q.Dw j).q - 1)

variable {T : Core D} {j : ℕ}

abbrev CMObj.fld (o : CMObj T j) : Type := @LamObj.K₁ _ _ _ _ T.Q.H.starRing _ _ _ _ _ o

instance (o : CMObj T j) : Field o.fld := @LamObj.fK _ _ _ _ T.Q.H.starRing _ _ _ _ _ o
instance (o : CMObj T j) : NumberField o.fld := @LamObj.nfK _ _ _ _ T.Q.H.starRing _ _ _ _ _ o
instance (o : CMObj T j) : Algebra T.Q.c.F o.fld := @LamObj.algK _ _ _ _ T.Q.H.starRing _ _ _ _ _ o

end GlobalTheory.IndefiniteRowSideFullHecke.MonomialNorms
