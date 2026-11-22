import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortLatticeSpanningSets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormComponentAddLeOfGramFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatFrameOfIsShortGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLarge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameBerg

theorem one_le_gap_of_strictAnti {N : ℕ} {v : Fin N → ℤ} (hv : StrictAnti v) {k : ℕ} (hk : k + 1 < N) :
    1 ≤ gap v k := by
  rw [gap, dif_pos hk]
  have := hv (show (⟨k, by omega⟩ : Fin N) < ⟨k + 1, hk⟩ from Fin.mk_lt_mk.2 (Nat.lt_succ_self k))
  omega

theorem gap_add {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

theorem antitone_of_gap_nonneg {N : ℕ} {v : Fin N → ℤ} (h : ∀ k, k + 1 < N → 0 ≤ gap v k) : Antitone v := by
  have key : ∀ d (a b : Fin N), (b : ℕ) = a + d → v b ≤ v a := by
    intro d
    induction d with
    | zero =>
      intro a b hab
      have e : b = a := Fin.ext (by simpa using hab)
      rw [e]
    | succ d ih =>
      intro a b hab
      have hc : (a : ℕ) + d < N := by omega
      have h1 := ih a ⟨(a : ℕ) + d, hc⟩ rfl
      have h2 := h ((a : ℕ) + d) (by omega)
      rw [gap, dif_pos (by omega)] at h2
      have e : b = ⟨(a : ℕ) + d + 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [e]
      linarith
  intro a b hab
  exact key ((b : ℕ) - a) a b (by have : (a : ℕ) ≤ b := hab; omega)

end GlobalTheory.FrameBerg

namespace GlobalTheory.FrameBerg

end GlobalTheory.FrameBerg
