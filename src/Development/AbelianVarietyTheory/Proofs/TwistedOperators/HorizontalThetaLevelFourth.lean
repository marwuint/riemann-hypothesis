import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmThetaLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFifth

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThetaArrowType

open GlobalTheory.Grid in

theorem sigOK_vert {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridPre R) (hG : G.Is) :
    ∀ i j, i ≤ D.R.m → j ≤ D.R.m → (G.V i j).V.SigOK
  | 0, 0, _, _ => D.sp.Y_sig 0
  | 0, j + 1, _, _ => by
    show (row0 R (j + 1)).V.SigOK
    by_cases h : j + 1 < D.R.m
    · rw [← nodeY_eq_chainVertexAtRowZero_of_lt R h]; exact D.sp.Y_sig _
    · rw [← nodeX_eq_chainVertexAtRowZero_of_ge R h]; exact D.sp.X'_sig
  | i + 1, j, hi, hj => (hG.spaces.vert i j hi hj).sigOK

theorem goodPar_of_node {D : D7} (N : GlobalTheory.Grid.Node D) (hV : N.V.SigOK) (τ : D.what₂.Tau) :
    GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) := by
  obtain ⟨hp, hq⟩ := GlobalTheory.TypeAtCompare.card_eq_of_congr (N.M.fr_unit τ) (N.M.fr_gram τ) (hV (tauE D τ))
  exact ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ,
    GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ), hp, hq⟩

end GlobalTheory.ThetaArrowType
