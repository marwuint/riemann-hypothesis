import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Bdy

section Algebra

variable (R : Type) [CommRing R] [IsDomain R]

abbrev intUnits : Subgroup (FractionRing R)ˣ := (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range

abbrev Cls : Type := (FractionRing R)ˣ ⧸ intUnits R

variable {R}

theorem cls_pow_eq_one [IsIntegrallyClosed R] {n : ℕ} (hn : n ≠ 0) (c : Cls R) (h : c ^ n = 1) : c = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have h' : x ^ n ∈ intUnits R := (QuotientGroup.eq_one_iff _).1 ((QuotientGroup.mk_pow _ _ _).trans h)
  obtain ⟨u, hu⟩ := h'
  have key : ∀ (y : (FractionRing R)ˣ) (v : Rˣ), Units.map (algebraMap R (FractionRing R)).toMonoidHom v = y ^ n →
      ∃ a : R, algebraMap R _ a = (y : FractionRing R) := fun y v hv => by
    refine IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_)
    have := congrArg Units.val hv
    rw [Units.val_pow_eq_pow_val] at this
    rw [← this]
    exact isIntegral_algebraMap
  obtain ⟨a, ha⟩ := key x u hu
  obtain ⟨b, hb⟩ := key x⁻¹ u⁻¹ (by rw [map_inv, hu, inv_pow])
  have hab : a * b = 1 := IsFractionRing.injective R (FractionRing R) (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
  exact (QuotientGroup.eq_one_iff _).2 ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, Units.ext ha⟩

instance [IsIntegrallyClosed R] : IsMulTorsionFree (Cls R) where
  pow_left_injective n hn a b h := by
    have : (a * b⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, show a ^ n = b ^ n from h, mul_inv_cancel]
    exact mul_inv_eq_one.1 (cls_pow_eq_one hn _ this)

end Algebra

section Coord

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

variable (Dg : DegData R (maximalIdeal R))

def coord (χ : Dg.toPre.X) : R := (GlobalTheory.BetaAdd.exists_coord Dg χ).choose

structure IsReading (O : Type) [Ring O] [StarRing O] [Module O Dg.toPre.X]
    (t : Dg.toPre.X → Dg.toPre.X → (FractionRing R)ˣ) : Prop where
  add_left : ∀ a a' b, t (a + a') b = t a b * t a' b
  symm : ∀ a b, t a b = t b a
  bal : ∀ (x : O) a b, t (x • a) b = t a (star x • b)
  coord : ∀ a b ra rb rab, PsiCoord Dg.toPre a ra → PsiCoord Dg.toPre b rb → PsiCoord Dg.toPre (a + b) rab →
    ∃ u : Rˣ, (t a b : FractionRing R) * algebraMap R _ (ra * rb * u) = algebraMap R _ rab

variable {Dg}

end Coord

end GlobalTheory.LocM.Bdy
