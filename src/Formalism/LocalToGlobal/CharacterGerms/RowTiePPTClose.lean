import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTEx
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOAct
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAllStart
import Formalism.LocalToGlobal.CharacterGerms.EndomorphismLimitIntegral
import Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallMain
import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelfEx
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf

namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_of_start2 (hS : AllStartSelfSt) : PTSelfSt :=
  ptSelf_of_start hS OActSelf.oActSelf_holds hStabSelf_holds

end Formalism.L2.FormalSeriesBounds
