import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupOfManyTorsionCharP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismOpenAffineLineAbelianSchemeConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonconstantRationalCurveNonproperGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharPSpecialisationSmoothCommGroupCurve
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ManyTorsionProper

theorem isProper_of_many_torsion_charZero : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  intro k _ _ _ G _ hG g hg m s hs hcard
  by_contra hnp
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hcard
    · exact h
  obtain ⟨P, hP, u, a, b, hu, hab⟩ := _root_.GlobalTheory.RatCurve.exists_rational_curve k G hG hnp
  obtain ⟨k', _, _, p, _, _, G', _, hG', hg', hm', ⟨s', hs', hc'⟩, P', hP', u', a', b', hu', hab'⟩ :=
    _root_.GlobalTheory.CharPSpec.exists_charP_specialization k G hG g hg m hm s hs P hP u a b hu hab
  have hpr : IsProper G'.hom :=
    _root_.GlobalTheory.SerreTateProperness.main k' p G' hG' g hg' m hm' s' hs' (by rw [hc']; exact hcard)
  exact hab' (_root_.GlobalTheory.NoRatCurve.maps_from_open_line_const k' G' (GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' _ G' hG' hpr) P' hP' u' a' b' hu')

end GlobalTheory.ManyTorsionProper
