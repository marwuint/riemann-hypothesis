import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterUnramifiedMu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridCharactersUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceNotNonsplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotNonSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceRatioRamified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterQuotientNotUnramifiedAtBasePlaceId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareMuDivChiRamifiedAtTwistPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceNotDvdDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryPlaceNotDvdDifferentBaseFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotDvdDifferentIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotRam

open GlobalTheory.WeilParts

variable {D : D7}

theorem unramAt_mul {e : AF D.host.F} {a b : (AE D)ˣ →* Circle} (ha : UnramAt e a) (hb : UnramAt e b) : UnramAt e (a * b) := by
  intro x h1 h2 h3
  rw [MonoidHom.mul_apply, ha x h1 h2 h3, hb x h1 h2 h3, one_mul]

theorem unramAt_pow {e : AF D.host.F} {a : (AE D)ˣ →* Circle} (ha : UnramAt e a) (n : ℕ) : UnramAt e (a ^ n) := by
  intro x h1 h2 h3
  rw [MonoidHom.pow_apply, ha x h1 h2 h3, one_pow]

theorem bottom_ram : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hr T Lc μ₀ hμ G => ?_⟩⟩
  intro W i j A A' WW X _ t v e he
  by_cases hS : v ∈ G.pl.S0 ∨ ∃ PP ∈ Lc.Q t, PP.under (𝓞 D.host.F) = v
  · right
    rw [mul_div_mul_right_eq_div]
    rcases hS with hS | ⟨PP, hPP, hPv⟩
    · refine ⟨_root_.GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt G μ₀ hμ t v e he hS, ?_, ?_⟩
      · rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
        · exact _root_.GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent G μ₀ hμ t v e he h0 i j
        · exact _root_.GlobalTheory.RamifiedOnLargePlaces.not_unramAt G μ₀ hμ t v e he h1 i j
      · rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
        · subst h0; exact GlobalTheory.T.auxiliary_place_not_dvd_different_base_field G
        · exact _root_.GlobalTheory.DiffSOne.not_dvd_differentIdeal large₂ hr v h1
    · refine ⟨_root_.GlobalTheory.SplitTwistPlaces.not_nonSplitAt G μ₀ hμ t v e he PP hPP hPv, ?_, hPv ▸ _root_.GlobalTheory.TwistPlDiff.under_not_dvd_differentIdeal Lc μ₀ hμ t PP hPP⟩
      by_cases h0 : v ∈ G.pl.S0
      · rcases G.pl.mem_S0_of_sum_eq.1 h0 with h0 | h1
        · exact _root_.GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent G μ₀ hμ t v e he h0 i j
        · exact _root_.GlobalTheory.RamifiedOnLargePlaces.not_unramAt G μ₀ hμ t v e he h1 i j
      · exact _root_.GlobalTheory.SqTop.not_unramAt_twist G μ₀ hμ t v e he h0 PP hPP hPv i j
  · left
    push_neg at hS
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.GridUnr.chi_eta_unramAt G μ₀ hμ t v e he hS.1 i
    exact ⟨unramAt_mul (_root_.GlobalTheory.BotTripleUnr.unramAt_mu G μ₀ hμ t v e he hS.1 hS.2 j) (unramAt_pow h2 _), unramAt_mul h1 (unramAt_pow h2 _)⟩

end GlobalTheory.BotRam

end
