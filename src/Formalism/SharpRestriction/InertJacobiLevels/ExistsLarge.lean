import Formalism.SharpRestriction.InertJacobiLevels.AsmIface

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

theorem FC.Large.mono {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large K' CH) (hK : K.le K') : C.Large K CH :=
  ⟨fun c hc => hK.1.trans (h.1 c hc), trivial, fun c hc => (hK.2.2.1 _).trans (h.2.2.1 c hc),
    fun c hc => (hK.2.2.2 _).trans (h.2.2.2 c hc)⟩

end Formalism.MainNotions.Inhab

end
