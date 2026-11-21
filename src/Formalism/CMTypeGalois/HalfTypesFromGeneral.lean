import Formalism.CMTypeGalois.CMTypeFrobenius.MQGalois
import Formalism.CMTypeGalois.CMTypeFrobenius.MQKummer
import Formalism.CMTypeGalois.StatementField
import Mathlib
import Formalism.CMTypeGalois.StatementGroup

open NumberField Ideal

namespace Formalism.Q3

theorem mqKummer : MQKummer := mqKummer_of mqGalois
end Formalism.Q3
