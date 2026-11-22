import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem algPtLa_moduli : N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → AlgPtLa Xo c :=
  fun h E _ _ _ H Dw l Xo c hpq =>
    Formalism.L2.PjFree.algPtLa_of (_root_.GlobalTheory.moduli_exists_numberField_point h E H Dw l Xo c hpq) _root_.GlobalTheory.locFld

end GlobalTheory
