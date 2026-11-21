import Mathlib
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.OneMemOffK
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl)
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec eulerFac seg)
open Formalism.UG (qV IsUnifV dosetInd)

namespace GlobalTheory.CompanionTheory.Ipf.Val

section Local

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev Cv : Type := v.adicCompletion K

def absV (x : Cv v) : ℝ := (WithZeroMulInt.toNNReal (NumberField.RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ)

def IsTame (δ : (Cv v)ˣ →* ℂˣ) : Prop :=
  (∀ x, ‖((δ x : ℂˣ) : ℂ)‖ = 1) ∧ ∀ x : (Cv v)ˣ, Valued.v ((x : Cv v) - 1) < 1 → δ x = 1

end Local

end GlobalTheory.CompanionTheory.Ipf.Val

end
