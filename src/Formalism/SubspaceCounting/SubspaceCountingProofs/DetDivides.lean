import Formalism.SubspaceCounting.StatementW

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {L : Type} [Field L] {r : ℕ}

def nMat (g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L[X] :=
  (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C)

lemma msDualMat_eq (g : GL (Fin r) L) : msDualMat g = (nMat g).transpose := rfl

end Formalism.G0.DetDividesP

end

namespace Formalism.G0.DetDividesP
end Formalism.G0.DetDividesP

namespace Formalism.G0.DetDividesP
end Formalism.G0.DetDividesP

namespace Formalism.G0.DetDividesP
end Formalism.G0.DetDividesP

namespace Formalism.G0.DetDividesP
end Formalism.G0.DetDividesP

namespace Formalism.G0.DetDividesP
end Formalism.G0.DetDividesP

namespace Formalism.G0.DetDividesP
end Formalism.G0.DetDividesP

namespace Formalism.G0.DetDividesP
end Formalism.G0.DetDividesP

namespace Formalism.G0.DetDividesP
end Formalism.G0.DetDividesP

namespace Formalism.G0.DetDividesP
end Formalism.G0.DetDividesP

namespace Formalism.G0

end Formalism.G0

