import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAlgHomOfFiniteTypeOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadPolarisedAbelianVarietyFinitelyManyP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureRationalThetaPointSubfield
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadModelFibreAtPointIsGivenVariety

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThetaDescent

theorem descends : ∀ (F Ω : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (n : ℕ), n.Prime → Odd n → (∀ j : ℕ, 1 ≤ j → ∃ (Ix : Type) (x : Ix → (baseOver (Sp Ω) ⟶ A.A)) (v : Ix → F), (∀ z : baseOver (Sp Ω) ⟶ A.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧ IsThetaPt A (n ^ j) x fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → ∃ (A₀ : PolAV (Sp F)) (a : A.A.left ⟶ A₀.A.left), IsGrpPullback A.A A₀.A (spMap em) a ∧ LBIso A.L (A₀.L.pull a) := by
  intro F Ω _ _ _ _ _ em A n hn ho hyp
  set J := ((n ^ 2) ^ 2) ^ A.g * A.g.factorial + 4 with hJ
  have hJ4 : 4 ≤ J := by omega
  have hb : ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ J :=
    lt_of_lt_of_le (by omega) (Nat.lt_pow_self hn.one_lt).le
  obtain ⟨Ix, x, v, hcov, hth⟩ := hyp J (by omega)
  obtain ⟨ζ, lev, v', hζ, hv'⟩ := _root_.GlobalTheory.ThetaDescentLevel.exists_level F Ω em A n J hn (by omega) Ix x v hcov hth
  obtain ⟨T, _, _, _, jT, P, φ, y₀, hft, hinj, hcomp, hP, hL, hy⟩ :=
    _root_.GlobalTheory.SpreadPolAV.exists_spread F Ω em A (Fin (2 * A.g)) lev.pt
  obtain ⟨t⟩ := GlobalTheory.exists_algHom_of_finiteType_of_isAlgClosed F T F
  exact _root_.GlobalTheory.MumCore.fibre_descends F Ω T em jT t hft hinj hcomp A P φ hP hL n J hn ho hJ4 hb ζ lev y₀ v' hζ hy hv'

end GlobalTheory.ThetaDescent
