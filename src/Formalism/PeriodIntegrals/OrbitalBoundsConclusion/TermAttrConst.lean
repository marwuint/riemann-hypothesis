import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GenericityConstantDoubleCosets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_function_const (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermFun D u u' :=
  PI.TermAttrConst.UnitaryGroupMassFormula.termFun_of PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u'

