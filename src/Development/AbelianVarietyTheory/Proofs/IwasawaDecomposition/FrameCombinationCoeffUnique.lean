import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.Proof.frame_combination_coeff_unique

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

variable {X : Scheme.{0}} {t : SAB H X} {k : Type} [CommRing k] {x : Sp k ⟶ X}

theorem comb_iff {m : ℕ} (u : Fin m → TanM x t.G) (a : Fin m → k) (w : Sp (DualNumber k) ⟶ t.G.left) :
    IsCombAtG t x (fun i => (tv (u i)).left) a w ↔ w = (tv (∑ i, a i • u i)).left := by
  have h0 := (GlobalTheory.LieMet.isComb_iff u a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨q, hq, hq'⟩ := h0
  obtain rfl : p = q := funext fun i => Over.OverMorphism.ext ((hp i).trans (hq i).symm)
  exact hq'

end

end GlobalTheory.Proof.frame_combination_coeff_unique
