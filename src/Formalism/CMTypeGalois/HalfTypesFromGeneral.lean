import Formalism.CMTypeGalois.CMTypeFrobenius.MQGalois
import Formalism.CMTypeGalois.CMTypeFrobenius.MQKummer
import Mathlib

open NumberField Ideal

namespace Formalism.Q3

theorem mqKummer : MQKummer := mqKummer_of mqGalois
end Formalism.Q3
