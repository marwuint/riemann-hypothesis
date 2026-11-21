import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolPrimeTo

end GlobalTheory.PolPrimeTo

namespace GlobalTheory.PolPrimeTo

section Push

variable {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)

theorem isMonHom_id_pow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) : IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  induction n with
  | zero => rw [pow_zero]; exact isMonHom_one A A
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

theorem push_id_pow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    haveI := isMonHom_id_pow A n
    push κ t ((𝟙 A) ^ n : A ⟶ A) = (n : R) • LinearMap.id := by
  induction n with
  | zero =>
    haveI := isMonHom_id_pow A 0
    rw [push_congr κ t (pow_zero (𝟙 A)), push_one, Nat.cast_zero, zero_smul]
  | succ n ih =>
    haveI := isMonHom_id_pow A n
    haveI := isMonHom_id_pow A (n + 1)
    haveI : IsMonHom ((𝟙 A) ^ n * 𝟙 A) := inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))
    rw [push_congr κ t (pow_succ (𝟙 A) n), push_mul, ih, push_id, Nat.cast_succ, add_smul, one_smul]

end Push

end GlobalTheory.PolPrimeTo

namespace GlobalTheory.PolPrimeTo

theorem bijective_push {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)
    {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (f : A ⟶ B) (h : B ⟶ A)
    [IsMonHom f] [IsMonHom h] (m : ℕ) (hm : IsUnit (m : R)) (e₁ : f ≫ h = 𝟙 A ^ m) (e₂ : h ≫ f = 𝟙 B ^ m) :
    Function.Bijective (push κ t f) := by
  haveI := isMonHom_id_pow A m
  haveI := isMonHom_id_pow B m
  have k₁ : ∀ x, push κ t h (push κ t f x) = (m : R) • x := fun x ↦ by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr κ t e₁, push_id_pow]; rfl
  have k₂ : ∀ y, push κ t f (push κ t h y) = (m : R) • y := fun y ↦ by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr κ t e₂, push_id_pow]; rfl
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨push κ t h ((↑hm.unit⁻¹ : R) • y), ?_⟩⟩
  · have e := congrArg (push κ t h) hxy
    rw [k₁, k₁] at e
    exact (hm.smul_left_cancel).1 e
  · rw [k₂, smul_smul, hm.mul_val_inv, one_smul]

end GlobalTheory.PolPrimeTo

namespace GlobalTheory.PolPrimeTo

end GlobalTheory.PolPrimeTo
