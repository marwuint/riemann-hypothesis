import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.RgJS

namespace PositivityTheory.Rg.BcB.Desc

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def InertThin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
  Summable fun w : {w : HeightOneSpectrum (𝓞 E) // ¬ IsSplitAt w} => (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹

end PositivityTheory.Rg.BcB.Desc

end
