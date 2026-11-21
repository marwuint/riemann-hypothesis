import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExtProof
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfRsmulRight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma finrank_eq (D : Formalism.BasicNotions.D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f]
  have hn : D.R.n = D.R.ord := rfl
  rw [hn]
  ring

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame
