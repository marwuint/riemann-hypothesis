import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions MvPolynomial

namespace Formalism.L2.Geo.Def

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable instance ssFin (n : ℕ) (ν : Fin n → ℕ) : Fintype (Formalism.GradedWeylDivisibility.ssIdx n n ν) :=
  (Formalism.GradedWeylDivisibility.sSIdxFinite n n ν).fintype

variable (D : D7)

end Formalism.L2.Geo.Def
