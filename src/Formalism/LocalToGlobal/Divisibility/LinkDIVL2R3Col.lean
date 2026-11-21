import Mathlib
import Formalism.LocalToGlobal.Divisibility.ConstantGeTwentyEight
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Formalism.LocalToGlobal.IndefiniteReal.FaceOf3

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef

section Face

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem linkDIV_L2R_face [IsTotallyComplex K] {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
    (Pk : IndefPkgR A fc cf C CH) (wf0 : (fc Pk.Zs).Df0.WF) (wf1 : (fc Pk.Zs).Df1.WF)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums Bs.J Pl) (u : (fc Pk.Zs).Dc.Mem)
    (Nu : Submodule (𝓞 K) (Fin ((fc Pk.Zs).Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (I : DivInputsR Pk.core R u Nu sg) : DivClausesR Pk.core R u Nu sg :=
  divClausesR_of wf0 wf1 Pk.core R u Nu sg I

end Face

end Formalism.L2.DIV
