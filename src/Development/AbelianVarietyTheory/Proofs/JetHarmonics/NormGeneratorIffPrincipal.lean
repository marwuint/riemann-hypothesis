import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.HostConjugateIdeal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq

noncomputable section

namespace GlobalTheory.NoCommonZeroCompare

section Quadratic

structure IsQuad {R : Type} [CommRing R] (c : R →+* R) (w : R) (k : ℤ) (d : ℕ) : Prop where
  prime : d.Prime
  four : 4 * k = 1 + d
  sq : w * w = w - k
  conj : c w = 1 - w
  span : ∀ x : R, ∃ a b : ℤ, x = a + b * w
  indep : ∀ a b : ℤ, (a : R) + b * w = 0 → a = 0 ∧ b = 0

variable {R : Type} [CommRing R] {c : R →+* R} {w : R} {k : ℤ} {d : ℕ}

end Quadratic

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

end GlobalTheory.NoCommonZeroCompare
