import Mathlib
import Development.AutomorphicArithmetic.CharacterBoxes.ExS
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Formalism.LocalToGlobal.FiniteTOf
import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AutomorphicArithmetic.CharacterBoxes.DesWin
import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Formalism.LocalToGlobal.NormalizedHeckeFactors.EtaClosed
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkGl
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkIRROfJoinEx
import Formalism.LocalToGlobal.NormalizedHeckeFactors.BaseRowsEqRecordRows
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Formalism.SharpRestriction.GlobalSchurBounds.PlugDgt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AdmissibleOfTransported
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GapClosed
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.NoColumnCase.LvlWire
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.LinkedMeasures.SlopeId
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.ValueBounds.SlopeMaxB
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.AdmissibleClasses.LinkGCl
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.SharpFunctions.FunTop
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.BuRationalOf
import Formalism.LocalToGlobal.Divisibility.SumLeEtaSumNum
import Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi
import Development.AutomorphicArithmetic.CharacterBoxes.Imprimitive

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc

def UpperTheory.EveryCharacter : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

