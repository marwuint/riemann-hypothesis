import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.CanonicalRigidImages
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeThick

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.CanonicalRigidImages

namespace GlobalTheory.GtCoordCompare

section Group

variable {S Y : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B] {q : G ⟶ B}
  {i : splitTorus S X ⟶ G} {L : LB Y} {K : Type} [Fintype K] {ε ε' : K → ℤ}

def WtGen (i : splitTorus S X ⟶ G) {φ' : K → (G.left ⟶ Y)} (x : LB.Gen (LB.LinComb L φ' ε')) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J), Good L z J →
    val x ((t ≫ i) * g).left z J = gm t.left z ⊤ (charUnit S X χ) * val x g.left z J

theorem act_comp [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) :
    ((t ≫ i) * g).left ≫ q.left = g.left ≫ q.left := by
  have e : ((t ≫ i) * g) ≫ q = g ≫ q := by
    rw [MonObj.mul_comp, Category.assoc, hi, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
  exact congrArg (fun f => f.left) e

theorem isWt_of_gs {V : G.left.Opens} {a : Γ(G.left, V)} {χ : X}
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ⊤ ≤ g.left ⁻¹ᵁ V → ∀ z : Z.left,
      gs ((t ≫ i) * g).left z V a = (gm t.left z ⊤ (charUnit S X χ)).val * gs g.left z V a) : IsWt i V a χ :=
  fun Z t g h₁ h₂ => fn_ext fun z hz => by
    rw [gs_mul _ z _ hz, gs_appLE _ _ _ _ _ z hz, gs_appLE _ _ _ _ _ z hz, Category.id_comp, Category.id_comp,
      h Z t g h₂ z]
    congr 1
    refine ((gs_pull (𝟙 _) t.left z ⊤ trivial _).trans ?_).symm
    rw [Category.id_comp, gs_unit _ z ⊤ trivial]

end Group

end GlobalTheory.GtCoordCompare
