import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.SharpRestriction.CuspSpanNormBounds.RotatedWeightedBound
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

noncomputable section

namespace Formalism.MainNotions.UniformConstantsAndStatements

export Formalism.MainNotions.S.UnitaryVolumeMass (Kng scalG)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants ValuativeRel IsDedekindDomain NumberField
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def adm5 (D : D7) (C : ℝ) : Prop :=
  UnitaryVolumeMass.stNG D C

structure AdmC where

  CNG : ℝ

  Ch : ℝ
  Cg : ℝ
  Cb : ℝ
  secondBesselConstant : ℝ
  Aw : ℝ
  Cgw : ℝ
  Cbw : ℝ

  CM : ℝ
  Ce : ℝ

  C1 : ℝ
  cL : ℝ

structure Ties (D : D7) (large₂ : SizeData₂ D) (Cn : ℝ) : Type 1 where
  X : TermTie D
  Y : ∀ u u' : D.what₂.Word, LoopTie D large₂ X u u' Cn

structure Given where
  C0 : ℝ
  Cg : ℝ
  cb : ℝ
  Cu : ℝ
  cT : ℝ
  CT : ℝ
  one_le_window_constant : 1 ≤ C0
  cb_pos : 0 < cb
  cT_pos : 0 < cT

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (g : Given)

def admF5 (C : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i) C
end Fam

end Formalism.MainNotions.UniformConstantsAndStatements
