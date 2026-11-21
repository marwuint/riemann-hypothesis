import Development.WeilBound.CoreStatements.MultihomogeneousSquares.ChooseTwoAdd
import Development.WeilBound.CoreStatements.MultihomogeneousSquares.SqOf
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Antisymmetry
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.APrime
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositive
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

def GoodTowerAntisymmetry : Prop :=
  Cmp.CmpSt → Given → Out.WeilSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)]
    (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem),
    o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I8 II (hhFl (CMType H) (D.p + D.q) II)

theorem good_tower_antisymmetry_of (hX : StX) (hAlg : StAlg) (hHt : StHt) (hSing : StSing) (hBase : StBase) (hCmp : StCmp)
    (hI8 : AntisymmetryFibreSquares) : GoodTowerAntisymmetry := by
  intro hC hG hW E _ _ _ H D Xo l c Y _ T o II hE hII hp hq
  obtain ⟨-, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  exact hI8 _root_.GlobalTheory.CompanionTheory.Ar.PB.Top.antisymmetry _root_.GlobalTheory.CompanionTheory.Ar.PB.agreementPos hG.2.2.2.2.2.2.2.2.2.1 II hII _ _ T _
    (sq_of (tie_of hX hAlg hHt hSing hBase) hCmp hC hG hW E H D Xo l c Y T o II hE hII hp hq)

end SquareStatements
