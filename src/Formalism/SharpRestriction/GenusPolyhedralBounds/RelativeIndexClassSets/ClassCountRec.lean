import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SatakeDualWeyl.DefsCS
import Formalism.ThetaLiftIndependence.Statement
import Formalism.HermitianLattices.StatementMass
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountFib
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountIdx
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountSurj
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.HermitianLattices.StatementLat
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountStab
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountGenIn
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGap
import Formalism.SharpRestriction.InertJacobiLevels.ExtraNum
import Formalism.SharpRestriction.InertJacobiLevels.ExtraRec
import Formalism.LocalRingCardinality.SpanPowerMembership.CodeRecordDiscriminantLevel
import Formalism.LocalRingCardinality.SpanPowerMembership.RowsMemBaseField
import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevM
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup

noncomputable section

namespace Formalism.MainNotions.Gaps.CC

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.MainNotions.Inhab Formalism.MainNotions.StandardLattice Formalism.MainNotions.Gaps.LG
open scoped TensorProduct

section Rec

variable {D : D7}

end Rec

section Base

variable {R : Ranks} (H : Host R) (T0 : ℕ) [hT0 : Fact T0.Prime] (pz0 : 𝓞 H.E)
  (hpz0 : (pz0 : H.E) * H.conj (pz0 : H.E) = (T0 : H.E))

end Base

end Formalism.MainNotions.Gaps.CC

end
