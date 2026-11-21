import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PlacesOverU
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ThreeNeSqAddSq

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.Published.LandherrModel Polynomial
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.UPel.HT.Gauss

instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem hζ : IsPrimitiveRoot ii 4 := IsCyclotomicExtension.zeta_spec 4 ℚ Qi

def pbO : PowerBasis ℤ (𝓞 Qi) := hζ.integralPowerBasis

def ζO : 𝓞 Qi := hζ.toInteger

theorem pbO_gen : pbO.gen = ζO := hζ.integralPowerBasis_gen

theorem pbO_dim : pbO.dim = 2 := by
  rw [pbO, hζ.integralPowerBasis_dim]; decide

theorem coe_ζO : (ζO : Qi) = ii := rfl

theorem ζO_sq : ζO * ζO = -1 := by
  ext; simp [coe_ζO, ii_mul]

theorem coordO (x : 𝓞 Qi) : ∃ a b : ℤ, x = a + b * ζO := by
  obtain ⟨f, hf, rfl⟩ := pbO.exists_eq_aeval x
  rw [pbO_dim] at hf
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one (by omega : f.natDegree ≤ 1)]
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  simp [pbO_gen]; ring

theorem minpoly_ζO : minpoly ℤ pbO.gen = cyclotomic 4 ℤ := by
  rw [pbO_gen, ← RingOfIntegers.minpoly_coe, coe_ζO]
  exact (cyclotomic_eq_minpoly hζ (by norm_num)).symm

theorem cyc4 (R : Type) [CommRing R] : cyclotomic 4 R = 1 + X ^ 2 := by
  rw [show (4 : ℕ) = 2 ^ (1 + 1) by norm_num, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [Finset.sum_range_succ]

def red : 𝓞 Qi →+* ZMod 5 :=
  (pbO.lift (2 : ZMod 5) (by rw [minpoly_ζO, cyc4]; simp; decide)).toRingHom

end GlobalTheory.UPel.HT.Gauss

namespace GlobalTheory.UPel.HT.Gauss

abbrev cO : 𝓞 Qi →+* 𝓞 Qi := (IsCMField.ringOfIntegersComplexConj Qi : 𝓞 Qi →+* 𝓞 Qi)

theorem cO_ζO : IsCMField.ringOfIntegersComplexConj Qi ζO = -ζO := by
  ext; simp [IsCMField.coe_ringOfIntegersComplexConj, coe_ζO, cc_ii]

end GlobalTheory.UPel.HT.Gauss

namespace GlobalTheory.UPel.HT.Gauss

theorem finrank_Qi : Module.finrank ℚ Qi = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 4) Qi (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

theorem coord_zero {a b : ℚ} (h : (a : Qi) + b * ii = 0) : a = 0 ∧ b = 0 := by
  have h2 : ((a ^ 2 + b ^ 2 : ℚ) : Qi) = 0 := by
    push_cast
    linear_combination ((a : Qi) - b * ii) * h + (b : Qi) ^ 2 * ii_mul
  have h3 : a ^ 2 + b ^ 2 = 0 := by exact_mod_cast h2
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

theorem li : LinearIndependent ℚ ![(1 : Qi), ii] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  apply coord_zero
  simpa [Algebra.smul_def] using hst

def bQ : Module.Basis (Fin 2) ℚ Qi :=
  basisOfLinearIndependentOfCardEqFinrank li (by rw [finrank_Qi]; simp)

theorem bQ_zero : bQ 0 = 1 := by simp [bQ]
theorem bQ_one : bQ 1 = ii := by simp [bQ]

theorem trace_ii : Algebra.trace ℚ Qi ii = 0 := by
  rw [Algebra.trace_eq_matrix_trace bQ, Matrix.trace_fin_two, Algebra.leftMulMatrix_apply,
    LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have e1 : Algebra.lmul ℚ Qi ii (bQ 0) = bQ 1 := by simp [bQ_zero, bQ_one]
  have e2 : Algebra.lmul ℚ Qi ii (bQ 1) = -bQ 0 := by simp [bQ_zero, bQ_one, ii_mul]
  rw [e1, e2, map_neg, bQ.repr_self, bQ.repr_self]; simp

theorem trace_coord (a b : ℚ) : Algebra.trace ℚ Qi ((a : Qi) + b * ii) = 2 * a := by
  have ha : (a : Qi) = algebraMap ℚ Qi a := (eq_ratCast _ a).symm
  have hb : (b : Qi) = algebraMap ℚ Qi b := (eq_ratCast _ b).symm
  rw [map_add, ha, hb, ← Algebra.smul_def, map_smul, trace_ii, smul_zero, add_zero,
    Algebra.trace_algebraMap, finrank_Qi, nsmul_eq_mul]; norm_num

theorem cc_coord (a b : ℚ) : IsCMField.complexConj Qi ((a : Qi) + b * ii) = a - b * ii := by
  simp [map_add, map_mul, map_ratCast, cc_ii]; ring

@[instance_reducible] def starQi : StarRing Qi where
  star := IsCMField.complexConj Qi
  star_involutive := IsCMField.complexConj_apply_apply Qi
  star_mul x y := by rw [map_mul, mul_comm]
  star_add x y := map_add _ x y

attribute [local instance] starQi

theorem star_eq (x : Qi) : star x = IsCMField.complexConj Qi x := rfl

def ψ : LinearMap.BilinForm ℚ Qi :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ Qi (-ii / 2 * x * IsCMField.complexConj Qi y))
    (fun x x' y => by simp only [mul_add, add_mul, map_add])
    (fun r x y => by rw [mul_smul_comm, smul_mul_assoc, map_smul])
    (fun x y y' => by simp only [map_add, mul_add])
    (fun r x y => by rw [map_rat_smul, mul_smul_comm, map_smul])

theorem ψ_apply (x y : Qi) : ψ x y = Algebra.trace ℚ Qi (-ii / 2 * x * IsCMField.complexConj Qi y) := rfl

theorem pos (x : Qi) (hx : x ≠ 0) :
    0 < LinearMap.trace ℚ Qi (LinearMap.mulLeft ℚ (x * star x)) := by
  change 0 < Algebra.trace ℚ Qi (x * star x)
  obtain ⟨a, b, rfl⟩ := exists_coord x
  have hab : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨rfl, rfl⟩; simp at hx
  have : ((a : Qi) + b * ii) * star ((a : Qi) + b * ii) = ((a ^ 2 + b ^ 2 : ℚ) : Qi) + ((0 : ℚ) : Qi) * ii := by
    rw [star_eq, cc_coord]; push_cast; linear_combination (-(b : Qi) ^ 2) * ii_mul
  rw [this, trace_coord]
  by_cases ha : a = 0
  · have hb : b ≠ 0 := fun hb => hab ⟨ha, hb⟩
    positivity
  · positivity

theorem exists_τ : ∃ τ : Qi →+* ℂ, τ ii = Complex.I := by
  let σ : Qi →+* ℂ := Classical.choice inferInstance
  have h : σ ii * σ ii = -1 := by rw [← map_mul, ii_mul]; simp
  have h' : σ ii = Complex.I ∨ σ ii = -Complex.I := by
    rw [← mul_self_eq_mul_self_iff, h]; simp
  rcases h' with h' | h'
  · exact ⟨σ, h'⟩
  · exact ⟨(starRingEnd ℂ).comp σ, by simp [h']⟩

def τ₀ : Qi →+* ℂ := exists_τ.choose

theorem τ₀_ii : τ₀ ii = Complex.I := exists_τ.choose_spec

end GlobalTheory.UPel.HT.Gauss

namespace GlobalTheory.UPel.HT.Gauss

attribute [local instance] starQi

def Λ : Submodule ℤ Qi := Submodule.span ℤ (Set.range ![(1 : Qi), ii])

theorem liZ : LinearIndependent ℤ ![(1 : Qi), ii] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h := coord_zero (a := s) (b := t) (by push_cast; simpa [zsmul_eq_mul] using hst)
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

def bΛ : Module.Basis (Fin 2) ℤ Λ := Module.Basis.span liZ

def E : LinearMap.BilinForm ℤ Λ :=
  LinearMap.mk₂ ℤ (fun x y => bΛ.repr x 1 * bΛ.repr y 0 - bΛ.repr x 0 * bΛ.repr y 1)
    (fun x x' y => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun r x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun r x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)

theorem E_apply (x y : Λ) : E x y = bΛ.repr x 1 * bΛ.repr y 0 - bΛ.repr x 0 * bΛ.repr y 1 := rfl

theorem bijective_of_gram {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 2) R M) (B : LinearMap.BilinForm R M) (h00 : B (b 0) (b 0) = 0)
    (h01 : B (b 0) (b 1) = -1) (h10 : B (b 1) (b 0) = 1) (h11 : B (b 1) (b 1) = 0) :
    Function.Bijective B := by
  have key : ∀ m j, B m (b j) = b.repr m 0 * B (b 0) (b j) + b.repr m 1 * B (b 1) (b j) := by
    intro m j
    conv_lhs => rw [← b.sum_repr m]
    simp only [Fin.sum_univ_two, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  constructor
  · intro m m' h
    have e0 := key m 0
    have e1 := key m 1
    have e0' := key m' 0
    have e1' := key m' 1
    rw [h] at e0 e1
    rw [h00, h10] at e0 e0'
    rw [h01, h11] at e1 e1'
    apply b.repr.injective
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; linear_combination e1 - e1'
    · simp only [Fin.mk_one, Fin.isValue]; linear_combination e0' - e0
  · intro f
    refine ⟨-(f (b 1)) • b 0 + f (b 0) • b 1, b.ext fun j => ?_⟩
    fin_cases j <;> simp [h00, h01, h10, h11]

end GlobalTheory.UPel.HT.Gauss

namespace GlobalTheory.UPel.HT.Gauss

attribute [local instance] starQi

def c : ℂ := ((Real.sqrt (1 / 2) : ℝ) : ℂ)

def m1 (A : Type) [CommRing A] : A ≃ₐ[A] Matrix (Fin 1) (Fin 1) A :=
  AlgEquiv.ofBijective (Algebra.ofId A _)
    ⟨fun a b h => by simpa [Matrix.algebraMap_eq_diagonal] using congrFun (congrFun h 0) 0,
     fun M => ⟨M 0 0, by ext i j; fin_cases i; fin_cases j; simp [Matrix.algebraMap_eq_diagonal]⟩⟩

end GlobalTheory.UPel.HT.Gauss

namespace GlobalTheory.UPel.HT

end GlobalTheory.UPel.HT
