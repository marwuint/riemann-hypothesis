import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianSchemeCharts.FinSys
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianSchemeCharts.IsOpenImmersionProdChart

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.AXO

variable {R : Type} [CommRing R]

theorem sep_tensor (A : Over (Sp R)) [IsSeparated A.hom] : IsSeparated (A ⊗ A).hom := by
  rw [Over.tensorObj_hom, Limits.pullback.condition]
  infer_instance

def Sq (P : Type) : Type := P × P

instance (P : Type) [SemilatticeInf P] : SemilatticeInf (Sq P) := inferInstanceAs (SemilatticeInf (P × P))

instance (P : Type) [Finite P] : Finite (Sq P) := inferInstanceAs (Finite (P × P))

end MainStatements.Hodge.Pf.AXO
