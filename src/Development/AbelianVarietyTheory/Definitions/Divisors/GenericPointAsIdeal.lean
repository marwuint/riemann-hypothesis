import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArithBase GlobalTheory.CechPic

namespace GlobalTheory.ArInt.Model

def IsConst (L : HermLB (𝟙 (Sp ℤ))) (t : ℝ) : Prop :=
  ∀ i, (∀ x, x ∈ L.B.U i) ∧ ∀ σ y, (L.φ σ).φ i y = 2 * t

variable {L M : HermLB (𝟙 (Sp ℤ))} {s t : ℝ}

theorem IsConst.dual (h : IsConst L s) : IsConst L.dual (-s) :=
  fun i => ⟨(h i).1, fun σ y => (congrArg (- ·) ((h i).2 σ y)).trans (by ring)⟩

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
private theorem lin_pow_eq_eval_sum_multinomial {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (m : ℕ) (r : ι → ℝ) :
    Ψ (_root_.GlobalTheory.ArInt.lin r ^ m) =
      MvPolynomial.eval r (∑ k ∈ (Finset.univ : Finset ι).piAntidiag m,
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k)
          ((Nat.multinomial Finset.univ k : ℝ) *
            Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1))) := by
  unfold _root_.GlobalTheory.ArInt.lin
  rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ∏ i, (MvPolynomial.C (r i) * MvPolynomial.X i) ^ k i =
      MvPolynomial.C (∏ i, r i ^ k i) *
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) (1 : ℝ) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [mul_pow, Finset.prod_mul_distrib, map_prod]
  rw [hk, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [← mul_assoc, ← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ), ← map_mul,
    ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
  simp
  ring

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
private theorem eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero {ι : Type} [Fintype ι]
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (m : ℕ)
    (hΨ : ∀ n : ι → ℤ, Ψ (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ m) = 0)
    {P : MvPolynomial ι ℝ} (hP : P.IsHomogeneous m) : Ψ P = 0 := by
  classical
  set Q : MvPolynomial ι ℝ := ∑ k ∈ (Finset.univ : Finset ι).piAntidiag m,
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k)
      ((Nat.multinomial Finset.univ k : ℝ) *
        Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1)) with hQdef
  have hQ : Q = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
    choose n hn using fun i => hx i (Set.mem_univ i)
    have hxn : x = fun i => (n i : ℝ) := funext fun i => (hn i).symm
    rw [map_zero, hxn, hQdef, ← lin_pow_eq_eval_sum_multinomial, hΨ]
  have hmon : ∀ d : ι →₀ ℕ, (Finsupp.weight 1) d = m →
      Ψ (MvPolynomial.monomial d 1) = 0 := by
    intro d hd
    have hmem : ⇑d ∈ (Finset.univ : Finset ι).piAntidiag m := by
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      rw [← hd, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
      simp
    have hc := congrArg (MvPolynomial.coeff d) hQ
    rw [hQdef, MvPolynomial.coeff_sum, Finset.sum_eq_single (⇑d)] at hc
    · rw [Finsupp.equivFunOnFinite_symm_coe, MvPolynomial.coeff_monomial, if_pos rfl,
        MvPolynomial.coeff_zero] at hc
      have hne : (Nat.multinomial Finset.univ ⇑d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.multinomial_pos _ _).ne'
      exact (mul_eq_zero.mp hc).resolve_left hne
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro heq
      apply hb
      rw [← heq]
      simp
    · intro h
      exact absurd hmem h
  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := hP (MvPolynomial.mem_support_iff.mp hd)
  have hsm : MvPolynomial.monomial d (MvPolynomial.coeff d P) =
      MvPolynomial.coeff d P • MvPolynomial.monomial d (1 : ℝ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul, hmon d hw, smul_zero]

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in

theorem _root_.GlobalTheory.ArInt.Model.isArFun_unique {k : Type} [CommRing k] {X : Scheme.{0}}
    [IsIntegral X] {p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {D E : ℕ} (hX : _root_.GlobalTheory.IsArithVar p E)
    {ι : Type} [Fintype ι] {L : ι → _root_.GlobalTheory.HermLB p}
    {Φ Φ' : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (h : _root_.GlobalTheory.ArInt.IsArFun L D Φ)
    (h' : _root_.GlobalTheory.ArInt.IsArFun L D Φ') :
    Φ = Φ' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hpow : ∀ n : ι → ℤ,
      (Φ - Φ') (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ (D + 1)) = 0 := by
    intro n
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact _root_.GlobalTheory.HermLB.IsSelfInter.unique hX
      (h1 n) (h1' n)
  have hhom : ∀ (P : MvPolynomial ι ℝ) (d : ℕ), P.IsHomogeneous d → Φ P = Φ' P := by
    intro P d hP
    by_cases hd : d = D + 1
    · subst hd
      exact sub_eq_zero.mp (eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero (Φ - Φ') (D + 1) hpow hP)
    · rw [h2 P d hd hP, h2' P d hd hP]
  refine LinearMap.ext fun P => ?_
  rw [← MvPolynomial.sum_homogeneousComponent P, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    hhom _ j (MvPolynomial.homogeneousComponent_isHomogeneous j P)

end GlobalTheory.ArInt.Model
