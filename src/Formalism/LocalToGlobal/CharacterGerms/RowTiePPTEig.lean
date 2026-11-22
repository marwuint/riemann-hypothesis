import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTClose
import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLieSelf

namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_of_eig (hE : RowTiePKey.KeyEigSt) : PTSelfSt :=
  ptSelf_of_start2 (allStartSelf_of_eig hE)

end Formalism.L2.FormalSeriesBounds
