import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeOfDetEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortLatticeSpanningSets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormComponentAddLeOfGramFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSeparationRegularDeterminant

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.ShortDet

theorem le_choose {f r p q : ℕ} (hf : 8 ≤ f) (hr : 100 ≤ r) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : p + q = r) :
    8 * f * r + 10 ≤ (f * p * q + 1).choose 2 := by
  have h1 : r ≤ p * q + 1 := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hq
    nlinarith [Nat.zero_le (a * b)]
  rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_assoc f, mul_assoc 8, Nat.le_div_iff_mul_le two_pos]
  generalize p * q = s at h1
  have h2 : f * r ≤ 2 * (f * s) := by
    rw [mul_left_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have h3 : 8 * 99 ≤ f * s := Nat.mul_le_mul hf (by omega)
  generalize f * s = N at h2 h3
  nlinarith

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem antitone_smul_hodgeWt {s : ℤ} (hs : 0 ≤ s) (τ : Psi H) : Antitone ((s • hodgeWt Dw) τ) := fun i j h => by
  have : (i : ℕ) ≤ j := h
  simp only [hodgeWt, CompHt.barWt, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> omega

theorem gap_smul_hodgeWt (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (s : ℤ) (τ : Psi H) : gap ((s • hodgeWt Dw) τ) (Dw.p - 1) = s := by
  have h : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega
  simp only [gap, dif_pos h, hodgeWt, CompHt.barWt, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> omega

theorem size_smul_hodgeWt {s : ℤ} (hs : 0 ≤ s) :
    ∑ τ, ∑ k, |((s • hodgeWt Dw) τ k : ℝ)| ≤ Module.finrank ℚ E * ((Dw.p + Dw.q : ℕ) * s) := by
  have h0 : (0 : ℝ) ≤ s := by exact_mod_cast hs
  refine (Finset.sum_le_card_nsmul _ _ (((Dw.p + Dw.q : ℕ) : ℝ) * s) fun τ _ => ?_).trans ?_
  · refine (Finset.sum_le_card_nsmul _ _ (s : ℝ) fun k _ => ?_).trans (by simp)
    simp only [hodgeWt, CompHt.barWt, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp [h0, abs_of_nonneg h0]
  · rw [nsmul_eq_mul, ← NumberField.Embeddings.card E ℂ]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Fintype.card_subtype_le _) (by positivity)

end Weight

end GlobalTheory.ShortDet
