import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformTorsionIsomorphism
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TateUniformizationInput
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotWeilIsGrpPullbackNoncomm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsShiftGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcClauseCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusExt GlobalTheory.ArcInputCompare GlobalTheory.ArcDataDescent GlobalTheory.LN
open scoped CategoryTheory.Obj

theorem qkToAkU_of_equiv {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} (hk : 1 ≤ k)
    {p q : QkPt D.toPre F k} (e : QkPt.Equiv D.toPre F p q) {x : TFK (R := R) F ⟶ A.A} (h : QkToAkU U F k p x) :
    QkToAkU U F k q x := by
  obtain ⟨z, hy, g, hι, hadd⟩ := e
  refine fun w₀ hw₀ => ⟨(h w₀ hw₀).1, fun θ hθ => ?_⟩
  obtain ⟨w, hw, H⟩ := (h w₀ hw₀).2 θ hθ
  obtain ⟨w₂, hw₂, H₂⟩ := QkShift.qk_shift globalFns_holds R D.toPre D.tau_bimult F k hk p q z g hy hι hadd w hw
  exact ⟨w₂, hw₂, fun t t' s s' a b c => H₂ s s' (H t t' s s' a b c)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
  {R : Type} [CommRing R] [IsDomain R] {f : O' →+* R} {u : R}

variable {Xo : Moduli D l} (Y : Model Xo c β)

end GlobalTheory.ArcClauseCompare
