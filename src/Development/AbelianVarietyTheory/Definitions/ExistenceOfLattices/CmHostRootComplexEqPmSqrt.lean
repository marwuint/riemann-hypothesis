import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.EqZeroOfOppositeSign
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriod
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumSumAndAllSignatures

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRatModel

open CompRat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_curve_model (H : Host E) : ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M)
    (P : Out.PolAV (Sp (𝓞 M))) (C : Curve H) (φ : C.P.A.left ⟶ P.A.left),
    IsGrpPullback C.P.A P.A (spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))) φ := by
  have hm := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) (by omega)
  obtain ⟨M, hM, w, P, v, hw, hg, -, -, hΛ, -⟩ :=
    cmCurve_closed H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  obtain ⟨Q, φ, hq, hφ, hL⟩ :=
    exists_baseChange polBaseChange_holds (spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))) P
  obtain ⟨u, hu⟩ := exists_isThetaUnif thetaUnifAV_all Q
  obtain ⟨c, hc, hl⟩ := hΛ Q φ ⟨hq, hφ, LBIso.symm hL⟩ u
  exact ⟨M, hM, P, ⟨Q, hq.trans hg, u, hu, c, hc, fun z => by rw [hl z, hw]⟩, φ, hφ⟩

instance nonempty_curve (H : Host E) : Nonempty (Curve H) := by
  obtain ⟨_, _, _, C, -⟩ := exists_curve_model H
  exact ⟨C⟩

end GlobalTheory.CompRatModel
