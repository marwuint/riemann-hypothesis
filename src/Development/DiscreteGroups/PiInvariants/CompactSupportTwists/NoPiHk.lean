import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.RgJS

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def locT (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) : Module.End ℂ (Sm E n) :=
  finRep E n (locGL E n w g)

def hk (w : HeightOneSpectrum (𝓞 E)) (R : Finset (GL (Fin n) (w.adicCompletion E))) : Module.End ℂ (Sm E n) :=
  ∑ r ∈ R, locT w r

end Defs

end DiscreteGroups.T1.G

end
