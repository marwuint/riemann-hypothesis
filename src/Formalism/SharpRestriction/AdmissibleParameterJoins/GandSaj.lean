import Formalism.SharpRestriction.Divisibility.ChainOperators.PerCol
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSx
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSy

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

theorem sgAtG_of {K : Consts} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C1 : ℝ} (hF : L.FDef)
    (hE : ErrDefs D L Xe lev K ce) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) : Formalism.MainNotions.WeightDegreeSizes.SgAtG D L Xe C1 :=
  fun i w hwi u hw => sumFE_atG_le hF hE hC1 hC i w hwi u hw

theorem family_type_prime_loss {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {C1 : ℝ} (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ Fm.cX.err.g) :
    Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 :=
  ⟨0, fun x hx _ i => sgAtG_of (local_compatibility_family Fm x hx i).fdef (Fm.ex x hx i).err hC1 hC⟩

end Formalism.MainNotions.J

end
