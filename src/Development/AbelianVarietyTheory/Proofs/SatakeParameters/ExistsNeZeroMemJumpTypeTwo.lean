import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalRingCardinality.DataDIV
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardTargetJumpsEqRank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ReindexedFiltrationComparison
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit

noncomputable section

namespace GlobalTheory.HTW.Rec.Model

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

instance decThickN {n b η : ℕ} (sz : ZMod n → ℕ) : DecidablePred (ThickN b η sz) := fun i => by
  unfold ThickN; infer_instance

end GlobalTheory.HTW.Rec.Model
