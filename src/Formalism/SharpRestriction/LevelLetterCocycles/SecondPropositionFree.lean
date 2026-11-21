import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.ClassMapStep
import Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
import Formalism.SharpRestriction.LevelLetterCocycles.FirstFrameStepImplication
import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingInput
import Formalism.SharpRestriction.LevelLetterCocycles.LemCStep

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def UnivLinkStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (Fo : FonOf D.loc D.locA HW), HerrClassMapsLocal D HW Fo → dvdR →
    invLiftR D HW → classMapR D HW → frameR D HW → modelFR D HW → u1R D HW → kapPiR D HW →
    u2R D HW → DownSlotProposition D HW → UpSlotProposition D HW → MixedSlotProposition D HW → univR D HW

end Formalism.MainNotions.N.Ln34

end
