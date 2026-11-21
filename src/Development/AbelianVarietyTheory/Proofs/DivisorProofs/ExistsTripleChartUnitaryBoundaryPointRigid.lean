import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointRigidTautologicalChartUnitaryBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartIsEtaleCompletionLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartBoundaryEquations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem uPre_of_boundary_pointRigid {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (hpq : 1 ≤ Dw.p + Dw.q)
    (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) (hns : NoSelfInt H.bar (min Dw.p Dw.q) φ)
    {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S)
    (hP : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) (hS : SepB Xo c φ j)
    (x : S) (hx : x ∉ Set.range j) : UPre Xo c φ j BD d x := by
  obtain ⟨k, _, m, e, C, ξ, hT, hy, hξ⟩ :=
    _root_.GlobalTheory.UCanon.exists_tautB_chart_at Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS x hx
  have hE := _root_.GlobalTheory.TautEtaleB.tautB_isEtaleCompletion Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  obtain ⟨hset, hred, a, ha, hbd⟩ :=
    _root_.GlobalTheory.UCanonBd.boundary_eq Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  exact ⟨k, inferInstance, m, e, C, ξ, a, hT.1, hy, hξ, hE, hred, hset, ha, hbd⟩

end GlobalTheory.UCanon
