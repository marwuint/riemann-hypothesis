import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugatorsDifferByCentralizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostAllPlacesTwistedUnitIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitEqNormAlmostAllPlacesStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocTriv

theorem map_starT {A R' C : Type} [CommRing A] [Algebra ℚ A] [CommRing R'] [Algebra ℚ R'] [Ring C] [Algebra ℚ C]
    (σ : C →+* Cᵐᵒᵖ) (f : A →ₐ[ℚ] R') (y : A ⊗[ℚ] C) :
    Algebra.TensorProduct.map f (AlgHom.id ℚ C) (starT σ A y).unop =
      (starT σ R' (Algebra.TensorProduct.map f (AlgHom.id ℚ C) y)).unop := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [starT_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, starT_tmul]; rfl
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

theorem map_conj_ext {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Type) [Field K] [Algebra ℚ K] {L : Type} [Field L]
    [Algebra ℚ L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L) (β₁ : G.Cˣ)
    (hc : ∀ x, ι (c x) = β₁ * sh G (ι x) * ((β₁⁻¹ : G.Cˣ) : G.C)) (z : K ⊗[ℚ] L) :
    Algebra.TensorProduct.map (AlgHom.id ℚ K) ι (Algebra.TensorProduct.map (AlgHom.id ℚ K) c z) =
      ((1 : K) ⊗ₜ[ℚ] (β₁ : G.C)) * (starT G.star K (Algebra.TensorProduct.map (AlgHom.id ℚ K) ι z)).unop *
        ((1 : K) ⊗ₜ[ℚ] ((β₁⁻¹ : G.Cˣ) : G.C)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, starT_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, AlgHom.id_apply,
      AlgHom.id_apply, hc]
    rfl
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy, mul_add, add_mul]

theorem map_invol {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] (c : L →ₐ[ℚ] L)
    (hcc : ∀ x, c (c x) = x) (z : K ⊗[ℚ] L) :
    Algebra.TensorProduct.map (AlgHom.id ℚ K) c (Algebra.TensorProduct.map (AlgHom.id ℚ K) c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hcc]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem selfDual_conj_eq_one {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing B] [Algebra R B]
    (ι : B →+* A) (hιR : ∀ r, ι (algebraMap R B r) = algebraMap R A r) (σ : A →+* Aᵐᵒᵖ) (cc : B →+* B) (β₁ : Aˣ)
    (X X₁ : Aˣ) (t t₁ : Rˣ) (a' : B) (m : Bˣ)
    (hc : ι (cc m) = ↑β₁ * (σ (ι m)).unop * ↑β₁⁻¹)
    (h1 : (X : A) * (ι a' * β₁) * (σ X).unop = algebraMap R A t)
    (h2 : (X₁ : A) * β₁ * (σ X₁).unop = algebraMap R A t₁) :
    ((X : A) * ι m * ↑X₁⁻¹) * ((X₁ : A) * ι (algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹)) * ↑X₁⁻¹) *
      (σ ((X : A) * ι m * ↑X₁⁻¹)).unop = 1 := by
  have hs1 : (σ (X₁ : A)).unop * (σ ((X₁⁻¹ : Aˣ) : A)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have ht1 : algebraMap R A ((t₁⁻¹ : Rˣ) : R) * algebraMap R A (t₁ : R) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have k1 : ((X₁⁻¹ : Aˣ) : A) * (σ ((X₁⁻¹ : Aˣ) : A)).unop = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * β₁ := by
    calc ((X₁⁻¹ : Aˣ) : A) * (σ ((X₁⁻¹ : Aˣ) : A)).unop
        = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * (((X₁⁻¹ : Aˣ) : A) * algebraMap R A (t₁ : R) *
            (σ ((X₁⁻¹ : Aˣ) : A)).unop) := by
          rw [← Algebra.commutes (t₁ : R), ← mul_assoc, ← mul_assoc, ht1, one_mul]
      _ = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * ((((X₁⁻¹ : Aˣ) : A) * X₁) * β₁ *
            ((σ X₁).unop * (σ ((X₁⁻¹ : Aˣ) : A)).unop)) := by
          rw [← h2]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, hs1, one_mul, mul_one]
  have hβ : (β₁ : A) * (σ (ι m)).unop = ι (cc m) * β₁ := by
    rw [hc, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  have hcm : cc (m : B) * cc ((m⁻¹ : Bˣ) : B) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hmE : (m : B) * (algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹)) * cc m =
      algebraMap R B (↑t⁻¹ * ↑t₁) * a' := by
    calc (m : B) * (algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹)) * cc m
        = algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (((m : B) * ↑m⁻¹) * (cc (m : B) * cc ↑m⁻¹)) := by ring
      _ = _ := by rw [Units.mul_inv, hcm, one_mul, mul_one]
  have hR : ((t₁⁻¹ : Rˣ) : R) * (((t⁻¹ : Rˣ) : R) * (t₁ : R)) * (t : R) = 1 := by
    calc ((t₁⁻¹ : Rˣ) : R) * (((t⁻¹ : Rˣ) : R) * (t₁ : R)) * (t : R)
        = (((t₁⁻¹ : Rˣ) : R) * (t₁ : R)) * (((t⁻¹ : Rˣ) : R) * (t : R)) := by ring
      _ = 1 := by rw [Units.inv_mul, Units.inv_mul, one_mul]
  set E := algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹) with hE
  clear_value E
  have eσ : (σ ((X : A) * ι m * ↑X₁⁻¹)).unop = (σ ((X₁⁻¹ : Aˣ) : A)).unop * (σ (ι m)).unop * (σ X).unop := by
    simp only [map_mul, MulOpposite.unop_mul, mul_assoc]
  rw [eσ]
  calc (X : A) * ι m * ↑X₁⁻¹ * (↑X₁ * ι E * ↑X₁⁻¹) *
        ((σ ((X₁⁻¹ : Aˣ) : A)).unop * (σ (ι m)).unop * (σ X).unop)
      = (X : A) * ι m * (((X₁⁻¹ : Aˣ) : A) * X₁) * ι E * (((X₁⁻¹ : Aˣ) : A) * (σ ((X₁⁻¹ : Aˣ) : A)).unop) *
          (σ (ι m)).unop * (σ X).unop := by simp only [mul_assoc]
    _ = (X : A) * ι m * ι E * (algebraMap R A ((t₁⁻¹ : Rˣ) : R) * (β₁ * (σ (ι m)).unop)) * (σ X).unop := by
          rw [Units.inv_mul, k1, mul_one]; simp only [mul_assoc]
    _ = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * ((X : A) * (ι ((m : B) * E * cc m) * β₁) * (σ X).unop) := by
          rw [hβ, show ι ((m : B) * E * cc m) = ι m * ι E * ι (cc m) by rw [map_mul, map_mul]]
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * (algebraMap R A (((t⁻¹ : Rˣ) : R) * (t₁ : R)) *
          ((X : A) * (ι a' * β₁) * (σ X).unop)) := by
          rw [hmE, map_mul, hιR]
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = 1 := by rw [h1, ← mul_assoc, ← map_mul, ← map_mul, hR, map_one]

theorem exists_finset_of_eventually {p : ℕ} {Q : AwayP p → Prop}
    (h : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), Q v) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v : AwayP p, v.1 ∉ S → Q v := by
  rw [Filter.eventually_cofinite] at h
  refine ⟨(h.image Subtype.val).toFinset, fun v hv => ?_⟩
  by_contra hq
  exact hv ((Set.Finite.mem_toFinset _).2 ⟨v, hq, rfl⟩)

theorem finite_above (p : ℕ) :
    ({v : HeightOneSpectrum ℤ | v.asIdeal = Ideal.span {(p : ℤ)}} : Set (HeightOneSpectrum ℤ)).Finite :=
  Set.Subsingleton.finite fun v hv w hw => HeightOneSpectrum.ext (hv.trans hw.symm)

theorem sh_mul' {p : ℕ} [Fact p.Prime] (G : HTGroup p) (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp [sh]

theorem sh_sh {p : ℕ} [Fact p.Prime] (G : HTGroup p) (x : G.C) : sh G (sh G x) = x := G.star_star x

theorem sh_inv_unit {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (hβ : sh G β = β) :
    sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
  have h : sh G β * sh G ((β⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← sh_mul', Units.inv_mul, sh_one_eq]
  rw [hβ] at h
  calc sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) * ((β : G.C) * sh G ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [h, mul_one]

end GlobalTheory.LocTriv
