import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLat
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapStab
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassSet
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.SharpRestriction.InertJacobiLevels.ExtraRec
import Formalism.LocalRingCardinality.SpanPowerMembership.TwistRecordRowDimensionZero
import Formalism.LocalRingCardinality.DataMink

noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.MainNotions.Inhab
open scoped TensorProduct

namespace Par

end Par

def clsPkg (X : Type) [Finite X] (d : ℕ) (hd : 0 < d) : ClsPkg where
  cls := fun i => match i with
    | 0 => X
    | _ + 1 => Empty
  clsFin := fun i => match i with
    | 0 => Fintype.ofFinite X
    | _ + 1 => inferInstanceAs (Fintype Empty)
  stab := fun _ _ => Unit
  stabGrp := fun _ _ => inferInstance
  stabFin := fun _ _ => inferInstance
  DGam := d
  DGam_pos := hd
  dvd := fun _ _ => by simp

end Formalism.MainNotions.Gaps.LG

end
