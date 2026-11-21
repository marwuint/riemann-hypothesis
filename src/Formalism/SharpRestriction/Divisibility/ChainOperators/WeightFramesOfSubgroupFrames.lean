import Formalism.PeriodIntegrals.NablaSpans.ExpansionCoeffValuationGe
import Formalism.PeriodIntegrals.NablaSpans.MinorProdSpanHasCompl
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinorSpanCompl

open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV.Lemmas

theorem kw_of_cutSB (h : CutKW.KWsb) : CutKW.KW := h minor_span_complement

end Formalism.MainNotions.DIV.Lemmas
