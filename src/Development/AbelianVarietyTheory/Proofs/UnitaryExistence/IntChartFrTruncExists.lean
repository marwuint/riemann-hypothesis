import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartTransportSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntChartFrTrunc
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralChartTransportToFramedPoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralChartsCompleteDvr

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

theorem GlobalTheory.IntChartTrunc.intChart_frTrunc_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT :=
  fun E _ _ _ H Dw l Xo c _ hstar T io y =>
    GlobalTheory.IntChartTrunc.exists_intChart_frTrunc _root_.GlobalTheory.intChart E H Dw l Xo c hstar (_root_.GlobalTheory.chartTransport_holds E H Dw l Xo c) T io y
