import Formalism.LocalToGlobal.Columns.TiedCls
import Formalism.LocalToGlobal.Columns.TiedXp
import Formalism.LocalToGlobal.Columns.TiedGl

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.UG Formalism.L2.DIV
open Formalism.L2.Forms (aOf skipOf fcOf InJ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rec

variable {d : ColDat} (a : ColArgs d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hCh : d.Ch.Ok)
  (hl : d.lev = colLevS d.Ch) (hlP : d.levP = (rowTyG d.Ch (rPsharp d.Ch)).inv)

end Rec

end Formalism.L2.Col
