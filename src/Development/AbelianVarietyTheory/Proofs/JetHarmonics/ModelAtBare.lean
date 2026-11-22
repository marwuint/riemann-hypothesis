import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.UnifAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.UniformizationClosedSplit

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Proof.ModelAtPrimeToLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
open scoped CategoryTheory.Obj

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (Xo : Moduli Dw l) (c : Coeff l)

end General

section Instance

variable {D : D7} {T : Top D}

theorem one_le_rank (h : LawsP T) {j : ℕ} (hj : InR D j) : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨h1, h2⟩ := hj
  rw [hp, hq]
  have h3 := D.R.m_add_three_le_k
  simp only [Ranks.sigW]
  omega

end Instance

end GlobalTheory.Proof.ModelAtPrimeToLevel
