import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.TiedFv
import Formalism.LocalToGlobal.Columns.TiedValAll
import Formalism.LocalToGlobal.Columns.TiedUpDn
import Formalism.LocalToGlobal.Columns.TiedGlRec
import Formalism.LocalToGlobal.Columns.TiedGlSplit
import Formalism.LocalToGlobal.Columns.TiedXpU
import Formalism.LocalToGlobal.Columns.InputsGenus
import Formalism.LocalToGlobal.Columns.TiedTilA
import Formalism.LocalToGlobal.Columns.TiedPer
import Formalism.LocalToGlobal.Columns.LevPackFrLat
import Formalism.LocalToGlobal.Columns.LastVectorMemSpan
import Formalism.LocalToGlobal.Columns.TiedAll

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col.V1

open Formalism.BasicNotions Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ColHyp (d : ColDat) : Prop where
  sp : SpStd d.toColBase
  host : HostHyp d
  row : RowSame d
  ch : d.Ch.Ok

  lev : d.lev = colLevS d.Ch
  levP : d.levP = (rowTyG d.Ch (rPsharp d.Ch)).inv

variable {d : ColDat} (a : ColArgs d) (h : ColHyp d)

end Formalism.L2.Col.V1
