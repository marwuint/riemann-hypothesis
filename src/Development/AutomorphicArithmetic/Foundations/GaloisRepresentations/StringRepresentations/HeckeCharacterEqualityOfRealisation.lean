import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecomposition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AdmissibleTemperedUnramified

noncomputable section

namespace UpperTheory.GalN

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem unr_part {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} {w : PlE H} :
    ∀ L : List (Part A.CG), A.unr (isoLoc N A L w) → ∀ p ∈ L, 1 ≤ p.d → A.unr (A.locG p.π w)
  | [], _, _, hp, _ => absurd hp List.not_mem_nil
  | q :: L, hun, p, hp, hd => by
    have hun' : A.unr (A.lpSum (spehLoc N A q w) (isoLoc N A L w)) := hun
    have h12 := (A.unr_sum _ _).1 hun'
    rcases List.mem_cons.1 hp with rfl | hp
    · have h := h12.1
      obtain ⟨d, hd'⟩ : ∃ d, p.d = d + 1 := ⟨p.d - 1, by omega⟩
      rw [GlobalTheory.StringDecomp.spehLoc_eq, hd', List.range_succ_eq_map] at h
      exact (A.unr_tw _ _).1 ((A.unr_sum _ _).1 h).1
    · exact unr_part L h12.2 p hp hd

end UpperTheory.GalN
