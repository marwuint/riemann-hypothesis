import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SplitAffineSpectral

def EvCob : Prop :=
  ∀ (G : Type) [Group G] (j : ℕ) (e : (Fin (j + 1) → G) → ℝ), Inv (MonoidHom.id G) e →
    ∀ z : Chn G (j + 1), IsCyc z → ev (MonoidHom.id G) (dC e) 1 z = 0

namespace GluingInclusion

end GluingInclusion

end PositivityTheory.KB.SplitAffineSpectral

end
