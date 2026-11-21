import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAl

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun.SetFromSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem finite_tup (p : PtAt ex Csz) : Finite p.P.T := by
  classical
  have h1 := p.charW.tup.mu_off
  have h2 := p.charW.tup.mu_used
  have : (Set.univ : Set p.P.T) ⊆ insert p.P.A3.A.μ0 (p.R.mu '' (p.R.twPl : Set _)) := fun t _ => by
    rcases h2 t with h | ⟨w, rfl⟩
    · exact Or.inl h
    · by_cases hw : w ∈ p.R.twPl
      · exact Or.inr ⟨w, hw, rfl⟩
      · exact Or.inl (h1 w hw)
  exact Set.finite_univ_iff.1 ((((p.R.twPl).finite_toSet.image _).insert _).subset this)

end GlobalTheory.BigTop.Fun.SetFromSize

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun

end
