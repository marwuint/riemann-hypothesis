import Formalism.SatakeDualWeyl.Statement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckebasic

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

def psiK {W : Type} (φ : G₁ × G₂ → W) (g : G₁ × G₂) : G₁ → W := fun h => φ (g * (h, 1))

end Formalism.UG.P
