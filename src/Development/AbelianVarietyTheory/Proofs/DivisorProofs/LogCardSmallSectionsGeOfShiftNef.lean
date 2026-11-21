import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLogNcardSeminormBallOneGe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBalls
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendsto
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_ball_one_ge_of_shift_nef : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a c M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a) (m * c) 1 := by
  intro hHS hAC k _ X _ p D hX P b s t hG a c M α t₀ hRep hSI hNef ε hε
  exact _root_.GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge X.functionField (fun m : ℕ => P.H (m * a) (m * c)) (fun m : ℕ => P.Bl (m * a) (m * c))
    (D + 1) (Nat.succ_pos D) (fun m => _root_.GlobalTheory.VolBr.Pair.isBallFam k X p P _ _)
    (fun m R => GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG _ _ R hAC)
    (α / (D + 1).factorial) ((D + 1) * gdeg M D / (D + 1).factorial) t₀
    (fun t ht => _root_.GlobalTheory.VolBr.lc_tendsto_of_rep hHS hAC k X p D hX P a c M α t₀ hRep hSI hNef t ht) ε hε

end GlobalTheory.VolBr
