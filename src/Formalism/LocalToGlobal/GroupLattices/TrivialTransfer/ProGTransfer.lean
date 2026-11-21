import Mathlib
import Formalism.LocalRingCardinality.DataLevel

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.L2.G.Triv

def IwProG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (v : HeightOneSpectrum (𝓞 F)) (g : ℕ), g.Prime → (g : 𝓞 F) ∈ v.asIdeal →
    IsProGrp g (iwU F k v)

end Formalism.L2.G.Triv

end
