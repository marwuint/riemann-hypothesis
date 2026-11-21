import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFormsEqSpanIntegralRationalFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCharacterTimesInverseUnitary

open NumberField

namespace GlobalTheory.CovTop

open GlobalTheory.BigTop Formalism.IndefR.FWT

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem rho_mem_WK (p : PtAt ex Csz) (i : Fin D.R.m) (g) (f) (hf : f ∈ (p.R.toRealDat.FW i).WK) :
    (p.R.toRealDat.FW i).ρ g f ∈ (p.R.toRealDat.FW i).WK := by
  by_cases hk : ActKeeps (κ := p.κ) p.O i
  · obtain ⟨c, hc⟩ := (p.fw.e i).surjective ⟨f, hf⟩
    obtain ⟨_, h2⟩ := (p.rhoGeo i).1 hk g c
    rw [hc] at h2
    rw [← h2]
    exact Subtype.property _
  · rw [(p.rhoGeo i).2 hk g]
    exact hf

end GlobalTheory.CovTop
