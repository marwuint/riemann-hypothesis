import Mathlib
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.Imports
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.TensorComplP

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F))

def phi : v.adicCompletion F ⊗[F] K →+*
    (∀ u : {u : HeightOneSpectrum (𝓞 K) // u.under (𝓞 F) = v}, u.1.adicCompletion K) :=
  RingHom.pi fun u => GlobalTheory.LFun.toCompl u.2

theorem phi_apply (y : v.adicCompletion F ⊗[F] K) (u : {u : HeightOneSpectrum (𝓞 K) // u.under (𝓞 F) = v}) :
    phi v y u = GlobalTheory.LFun.toCompl u.2 y := rfl

end CompanionTheory.Rg.BcB.G3.TensorComplP

end
