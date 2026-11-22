import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfThickeningsLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianLiftAmpleBundle

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumLift

theorem ker_factor_sq {R : Type} [CommRing R] (J : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R ⧸ J ^ (e + 1 + 1) →+* R ⧸ J ^ (e + 1)) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx hy
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have h := Ideal.mul_mem_mul hx hy
  rw [← pow_add] at h
  exact Ideal.pow_le_pow_right (by omega) h

end GlobalTheory.MumLift
