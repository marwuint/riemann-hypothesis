import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Development
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PhiMain
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.admitted
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.CupLZeroRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.CupCastRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.Geo
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bock
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.EqZeroOfCast
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SecMapZero

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

structure Chapters : Prop where
  rin : ∀ (l : ℕ) [Fact l.Prime], E.RIn l
  et : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), E.EtMap l K
  uniq : E.FirstChernUniqueEtale
  main : ∀ (l : ℕ) [Fact l.Prime], B.Main l
  compat : ∀ (l : ℕ) [Fact l.Prime], B.Compat l
  compatH : ∀ (l : ℕ) [Fact l.Prime], B.CompatH l
  c1 : ∀ (l : ℕ) [Fact l.Prime], B.FirstChernCompatible l
  p : BocksteinBaseChangeP

def CstSmooth : Prop := SmoothModelCrystalline ∧ DeRhamComparisonSmooth ∧ CrysPhi

end CrystallineSemistableComparison
