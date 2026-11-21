import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqOfSecConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.RelTests

section Tors
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem isNsmul_b {k : ℕ} {g h : GtPtF D F} (H : GtPtF.IsNsmul k g h) : h.b = g.b ^ k := by
  obtain ⟨gs, h0, hs, hl⟩ := H
  have key : ∀ (n : ℕ) (hn : n < k + 1), (gs ⟨n, hn⟩).b = g.b ^ n := by
    intro n
    induction n with
    | zero => intro hn; rw [pow_zero]; exact h0.1
    | succ n ih =>
      intro hn
      have e := (hs ⟨n, by omega⟩).1
      rw [pow_succ, ← ih (by omega)]
      exact e
  rw [← hl]
  exact key k (Nat.lt_succ_self k)

end Tors

end GlobalTheory.UU.RelTests
end
