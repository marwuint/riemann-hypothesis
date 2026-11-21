import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm

noncomputable section

namespace GlobalTheory.Core.Rk.SWQ

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart)

section Local

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {m n N : ℕ}

def IntM {ι κ : Type} (x : Matrix ι κ (w.adicCompletion E)) : Prop := ∀ i j, x i j ∈ Ov E w

end Local

section Adelic

variable {D : D7} {q : FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}

def cw (h : w.under (𝓞 D.host.F) = q) : AE D →+* w.adicCompletion D.host.E := (toCompl h).comp (compFin D.host.F D.host.E q)

def offM (q : FinPl D) {m n : ℕ} (x : Mx D m n) : Mx D m n :=
  x - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) • x

end Adelic

end GlobalTheory.Core.Rk.SWQ

end
