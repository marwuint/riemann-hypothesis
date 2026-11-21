import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftSL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexStabilizer

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.K4

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem eval_liftK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (a : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))) :
    AdicCompletion.eval (idl l) (X.Kl l) n (liftK X l n a) = a :=
  Classical.epsilon_spec (AdicCompletion.eval_surjective (idl l) (X.Kl l) n a)

theorem eval_clsK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {w : X.K} (h : w ≠ 0) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n w) = X.cls l n (Units.mk0 w h) := by
  unfold clsK
  rw [dif_pos h]
  exact eval_liftK X l n _

theorem clsK_zero (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : clsK X l n 0 = 0 := by
  unfold clsK
  exact dif_neg fun h => h rfl

theorem cls_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f g : X.Kˣ) :
    X.cls l n (f * g) = X.cls l n f + X.cls l n g := by
  unfold Tower.cls
  rw [ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]

theorem map_liftSL (M : ℕ) (g : SL(2, ZMod M)) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M g) = g :=
  Classical.epsilon_spec (GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M g)

theorem exists_place_over (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] :
    ∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 := by

  let R : Subring Ω := (Int.castRingHom Ω).range
  let x : R := ⟨(l : Ω), RingHom.mem_range.2 ⟨(l : ℤ), by simp⟩⟩
  have hI : Ideal.span {x} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hx
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hx
    obtain ⟨n, hn⟩ := RingHom.mem_range.1 y.2
    have h1 : ((l * n : ℤ) : Ω) = 1 := by
      have hv := congrArg Subtype.val hy
      rw [Subring.coe_mul, Subring.coe_one, ← hn] at hv
      rw [Int.cast_mul, Int.cast_natCast]
      exact hv
    have h2 : (l : ℤ) * n = 1 := by
      have h5 : algebraMap ℚ Ω (((l * n : ℤ)) : ℚ) = algebraMap ℚ Ω 1 := by
        rw [map_intCast, map_one]
        exact h1
      exact_mod_cast (algebraMap ℚ Ω).injective h5
    have h3 := Int.eq_one_or_neg_one_of_mul_eq_one h2
    have h4 := (Fact.out : l.Prime).two_le
    omega
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring (Ideal.span {x}) hI
  exact ⟨B, (ValuationSubring.mem_nonunits_iff B).1 (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩

theorem cycMod_surjective (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) :
    Function.Surjective (cycMod ℚ Ω l r) := by
  intro x
  obtain ⟨A, hA⟩ := exists_place_over Ω l
  obtain ⟨s, hs⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA r x
  exact ⟨_, hs⟩

end GlobalTheory.K4
