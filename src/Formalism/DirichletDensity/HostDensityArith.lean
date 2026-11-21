import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
import Formalism.DirichletDensity.DirichletDensityProofs.MQDiscr
import Formalism.DirichletDensity.DirichletDensityProofs.APLogDensity
import Mathlib
import Formalism.DirichletDensity.Statement
import Formalism.CMTypeGalois.HalfTypesFromGeneral

namespace Formalism.HF.Final

theorem quadDiscr : Formalism.HF.QuadDiscr := Formalism.HF.quadDiscr
theorem mqDiscr : Formalism.HF.MQDiscr := Formalism.HF.mqDiscr_of quadDiscr
end Formalism.HF.Final
