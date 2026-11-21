import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EmbeddingPermutesLetters
import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EmbTraceSum

namespace Formalism.MainNotions.Ext

theorem traceSum_holds : TraceSum := sumEqTrace_holds

theorem trace_sum_over_letters_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLatticesGL3.TraceMapNormalisation D := trace_sum_over_letters traceSum_holds D

end Formalism.MainNotions.Ext
