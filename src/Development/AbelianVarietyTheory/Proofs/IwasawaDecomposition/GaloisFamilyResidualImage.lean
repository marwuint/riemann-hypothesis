import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.ChiOneRead

theorem localIdele_eq {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    Neutral.B1.localIdele E P u = Units.map (Formalism.L2.NC.locM P) u := by
  classical
  apply Units.ext
  rfl

theorem sqrt_zpow (q : ℕ) (r : ℕ) (t nV : ℕ) (h : nV = r + t) :
    ((Real.sqrt q : ℝ) : ℂ) ^ (-(r : ℤ)) = ((q : ℕ) : ℂ) ^ (((((t : ℝ) - 1) / 2 + (1 - (nV : ℝ)) / 2) : ℝ) : ℂ) := by
  subst h
  have e : (((t : ℝ) - 1) / 2 + (1 - ((r + t : ℕ) : ℝ)) / 2) = -(r : ℝ) / 2 := by push_cast; ring
  rw [e]
  rw [show ((q : ℕ) : ℂ) = ((q : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast; ring

end GlobalTheory.ChiOneRead
