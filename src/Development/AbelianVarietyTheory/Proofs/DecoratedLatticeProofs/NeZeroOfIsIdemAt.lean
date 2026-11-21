import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.LevelPlaces

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7}

theorem splitAt_of {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} {ε : AF D.host.F} (he : IsSplitIdem D e)
    (hε : IsPlaceIdem D v ε) (h : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitAt D v e := by
  obtain ⟨α, rfl, h3, h4⟩ := hε
  have : α = singleV D.host.F v 1 := af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h3, evalV_singleV_same]
    · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
  subst this
  exact ⟨he.1, he.2.1, h⟩

theorem ne_zero_of_isIdemAt {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt e P) : e ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  exact ((hP.2 x hx0).1 hx) (by rw [zero_mul, map_zero]; exact zero_mem _)

end GlobalTheory.LevelPlaces
