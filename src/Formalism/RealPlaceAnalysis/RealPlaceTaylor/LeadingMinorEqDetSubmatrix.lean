import Formalism.RealPlaceAnalysis.LminorPos

open Matrix
open scoped ComplexOrder

noncomputable section

namespace Formalism.REAL

lemma leading_minor_eq_det_submatrix {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) (i : Fin (n + 1)) :
    lminor x i = (x.submatrix (Fin.castLE (Nat.lt_succ_iff.mp i.isLt))
      (Fin.castLE (Nat.lt_succ_iff.mp i.isLt))).det := rfl

end Formalism.REAL
