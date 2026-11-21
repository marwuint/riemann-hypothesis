import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfIntegralGaugedFormalGroupLaw
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsPairData
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairDataStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndPairPlaces

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem cartHyp_of_formalBiextension : CartFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p
  exact _root_.GlobalTheory.RowLaw.cartHyp_of_rlaw C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p)
    (_root_.GlobalTheory.hasProj_pairData C V O dd Y d I p) (_root_.GlobalTheory.TeichPair.hasTeich C V O dd Y d I p)

end GlobalTheory
