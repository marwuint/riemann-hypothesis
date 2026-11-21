import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.ParConsts

open Matrix MeasureTheory TensorProduct
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.RadialRules

open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (lenI AEq mid3 wnormSq)

def adm1 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaBCont CB

def adm2 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaBAdj CB

def adm3 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_cap

def ArchimedeanSignatureMatching (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_anti

def adm5 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_branch

def adm6 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_wigner

def adm10 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaBRad CB

def RulesGauge (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_gauge

def ResidueBoundAlt (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stA_herm C

def RulesCapelli (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_capelli

def RadialRulesCombined (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanTopCondition

def RulesSigns (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_signs

def adm7 (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  RulesGauge D ∧ ResidueBoundAlt D C ∧ RulesCapelli D ∧ RadialRulesCombined D ∧ RulesSigns D

def RulesRTT (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_rtt

def RulesDeterminant (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_det

def adm8 (D : Formalism.BasicNotions.D7) : Prop := RulesRTT D ∧ RulesDeterminant D

def RulesWordModule (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_module C

def RulesFormHermitian (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_rrherm C

def RulesTelescoping (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_tele

def RadialRuleLeadingEntry (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_entry

def RulesDuality (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_dual C

def RulesPlaneWave (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanWaveCondition

def adm9 (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  RulesWordModule D C ∧ RulesFormHermitian D C ∧ RulesTelescoping D ∧ RadialRuleLeadingEntry D ∧ RulesDuality D C ∧ RulesPlaneWave D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def aux₃ (_D : Formalism.BasicNotions.D7) (C Cv C1 C2 : ℝ) : Prop := S.UnitaryLevelOperators.stLevel C Cv C1 C2

def admitted (D : Formalism.BasicNotions.D7) (CB Ca : ℝ) : Prop :=
  adm1 D CB ∧ adm2 D CB ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D Ca ∧ adm8 D ∧ adm9 D Ca ∧ adm10 D CB

theorem lemma_B_three_iff (D : Formalism.BasicNotions.D7) (CB : ℝ) : (adm1 D CB ∧ adm2 D CB ∧ adm10 D CB) ↔ LemmaBThreeClauses CB := Iff.rfl

theorem radial_statement_indep_datum (D D' : Formalism.BasicNotions.D7) (C Cv C1 C2 : ℝ) : aux₃ D C Cv C1 C2 ↔ aux₃ D' C Cv C1 C2 := Iff.rfl

theorem Adm_indep (D D' : Formalism.BasicNotions.D7) (CB Ca : ℝ) : admitted D CB Ca ↔ admitted D' CB Ca := Iff.rfl

end Formalism.MainNotions.RadialRules
