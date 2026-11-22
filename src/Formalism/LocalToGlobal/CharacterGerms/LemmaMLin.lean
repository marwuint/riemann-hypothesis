import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.SecondWayHolds
import Formalism.FrobeniusBaseCase.Statement

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.BaseCaseIdentities (OrdGE NoConst)

section General

variable {C : Type*} [Field C] {σ τ : Type*}

theorem ordGE_one_iff (f : MvPowerSeries τ C) : OrdGE 1 f ↔ constantCoeff f = 0 := by
  constructor
  · intro h
    have := h 0 (by simp)
    simpa using this
  · intro h A hA
    have hA0 : A = 0 := by
      have : A.degree = 0 := by omega
      exact (Finsupp.degree_eq_zero_iff A).1 this
    subst hA0
    simpa using h

theorem ordGE_zero (f : MvPowerSeries τ C) : OrdGE 0 f := fun _ h => absurd h (Nat.not_lt_zero _)

theorem ordGE_finset_prod {ι : Type*} (s : Finset ι) (n : ι → ℕ) (f : ι → MvPowerSeries τ C)
    (h : ∀ i ∈ s, OrdGE (n i) (f i)) : OrdGE (∑ i ∈ s, n i) (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using ordGE_zero (1 : MvPowerSeries τ C)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact Formalism.BaseCaseIdentities.OrdGE.mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ordGE_finsupp_prod (a : σ → MvPowerSeries τ C) (ha : ∀ s, OrdGE 1 (a s)) (d : σ →₀ ℕ) :
    OrdGE d.degree (d.prod fun s n => a s ^ n) := by
  have h := ordGE_finset_prod d.support (fun s => d s) (fun s => a s ^ d s)
    (fun s _ => Formalism.BaseCaseIdentities.OrdGE.pow (ha s) (d s))
  exact h

theorem hasSubst_of_ordGE [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s)) :
    HasSubst a := hasSubst_of_constantCoeff_zero fun s => (ordGE_one_iff _).1 (ha s)

theorem coeff_subst_congr [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {F G : MvPowerSeries σ C} {N : ℕ} (h : ∀ d : σ →₀ ℕ, d.degree ≤ N → coeff d F = coeff d G)
    (e : τ →₀ ℕ) (he : e.degree ≤ N) : coeff e (subst a F) = coeff e (subst a G) := by
  rw [coeff_subst (hasSubst_of_ordGE ha), coeff_subst (hasSubst_of_ordGE ha)]
  refine finsum_congr fun d => ?_
  by_cases hd : d.degree ≤ N
  · rw [h d hd]
  · rw [ordGE_finsupp_prod a ha d e (by omega), smul_zero, smul_zero]

theorem ordGE_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {F : MvPowerSeries σ C} {n : ℕ} (hF : OrdGE n F) : OrdGE n (subst a F) := by
  intro e he
  rw [coeff_subst (hasSubst_of_ordGE ha)]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : d.degree < n
  · rw [hF d hd, zero_smul]
  · rw [ordGE_finsupp_prod a ha d e (by omega), smul_zero]

def killV (P : σ → Prop) (F : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun μ => if ∀ w ∈ μ.support, P w then coeff μ F else 0

theorem dVar_eq_pderiv {C : Type} [Field C] {σ : Type} (w : σ) (F : MvPowerSeries σ C) :
    dVar w F = pderiv C w F := by
  ext μ
  rw [coeff_pderiv]
  show ((μ w + 1 : ℕ) : C) * coeff (μ + Finsupp.single w 1) F = _
  push_cast
  ring

theorem ordGE_pderiv {F : MvPowerSeries σ C} {n : ℕ} (hF : OrdGE (n + 1) F) (w : σ) :
    OrdGE n (pderiv C w F) := by
  intro e he
  rw [coeff_pderiv, hF _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]

theorem pderiv_subst_coe [Fintype σ] {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (b : τ)
    (p : MvPolynomial σ C) :
    pderiv C b (subst a (p : MvPowerSeries σ C)) =
      ∑ w, pderiv C b (a w) * subst a (pderiv C w (p : MvPowerSeries σ C)) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.coe_C]
    have : subst a (MvPowerSeries.C r : MvPowerSeries σ C) = MvPowerSeries.C r := by
      rw [← substAlgHom_apply ha]
      exact (substAlgHom ha).commutes r
    rw [this, pderiv_C]
    symm
    refine Finset.sum_eq_zero fun w _ => ?_
    have h0 : subst a (0 : MvPowerSeries σ C) = 0 := by
      rw [← substAlgHom_apply ha, map_zero]
    rw [pderiv_C, h0, mul_zero]
  | add p q hp hq =>
    rw [MvPolynomial.coe_add, subst_add ha, map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_add, subst_add ha, mul_add]
  | mul_X p w0 hp =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, subst_X ha, Derivation.leibniz, hp]
    have h1 : ∀ w, pderiv C b (a w) * subst a (pderiv C w ((p : MvPowerSeries σ C) * X w0)) =
        a w0 * (pderiv C b (a w) * subst a (pderiv C w (p : MvPowerSeries σ C))) +
          (if w = w0 then pderiv C b (a w0) * subst a (p : MvPowerSeries σ C) else 0) := by
      intro w
      rw [Derivation.leibniz, subst_add ha, smul_eq_mul, smul_eq_mul, subst_mul ha, subst_mul ha,
        subst_X ha]
      by_cases hw : w = w0
      · subst hw
        rw [pderiv_X_self, if_pos rfl]
        have : subst a (1 : MvPowerSeries σ C) = 1 := by
          rw [← substAlgHom_apply ha, map_one]
        rw [this]
        ring
      · rw [pderiv_X_of_ne (Ne.symm hw), if_neg hw]
        have : subst a (0 : MvPowerSeries σ C) = 0 := by
          rw [← substAlgHom_apply ha, map_zero]
        rw [this]
        ring
    simp only [h1]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ w0, if_pos (Finset.mem_univ _),
      ← Finset.mul_sum, smul_eq_mul, smul_eq_mul]
    ring

theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s)) (b : τ)
    (H : MvPowerSeries σ C) :
    pderiv C b (subst a H) = ∑ w, pderiv C b (a w) * subst a (pderiv C w H) := by
  have hs := hasSubst_of_ordGE ha
  ext e
  obtain ⟨p, hp⟩ : ∃ p : MvPolynomial σ C, p = truncTotal (e.degree + 2) H := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : MvPowerSeries σ C, R = H - (p : MvPowerSeries σ C) := ⟨_, rfl⟩
  have hRo : OrdGE (e.degree + 2) R := by
    intro d hd
    rw [hR, map_sub, MvPolynomial.coeff_coe, hp, coeff_truncTotal _ hd, sub_self]
  have hH : H = (p : MvPowerSeries σ C) + R := by rw [hR]; ring
  have hL : coeff e (pderiv C b (subst a R)) = 0 :=
    ordGE_pderiv (n := e.degree + 1) (ordGE_subst ha hRo) b e (by omega)
  have hRr : coeff e (∑ w, pderiv C b (a w) * subst a (pderiv C w R)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    have h1 : OrdGE (0 + (e.degree + 1)) (pderiv C b (a w) * subst a (pderiv C w R)) :=
      Formalism.BaseCaseIdentities.OrdGE.mul (ordGE_zero _) (ordGE_subst ha (ordGE_pderiv (n := e.degree + 1) hRo w))
    exact h1 e (by omega)
  have hsum : ∑ w, pderiv C b (a w) * subst a (pderiv C w H) =
      (∑ w, pderiv C b (a w) * subst a (pderiv C w (p : MvPowerSeries σ C))) +
        ∑ w, pderiv C b (a w) * subst a (pderiv C w R) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hH, map_add, subst_add hs, mul_add]
  rw [hsum, map_add, hRr, add_zero, ← pderiv_subst_coe hs, hH, subst_add hs, map_add, map_add, hL,
    add_zero]

end General

section Lin

variable {C : Type*} [Field C] {σ τ : Type*} [Fintype τ]

def linS (M : τ → σ → C) : σ → MvPowerSeries τ C := fun w => ∑ c, M c w • (X c : MvPowerSeries τ C)

theorem ordGE_linS (M : τ → σ → C) (w : σ) : OrdGE 1 (linS M w) := by
  unfold linS
  refine Formalism.BaseCaseIdentities.OrdGE.sum _ fun c _ => ?_
  rw [smul_eq_C_mul]
  exact Formalism.BaseCaseIdentities.OrdGE.C_mul _ (Formalism.BaseCaseIdentities.OrdGE.X c)

theorem hasSubst_linS [Finite σ] (M : τ → σ → C) : HasSubst (linS M) :=
  hasSubst_of_ordGE (ordGE_linS M)

theorem pderiv_linS (M : τ → σ → C) (b : τ) (w : σ) :
    pderiv C b (linS M w) = MvPowerSeries.C (M b w) := by
  unfold linS
  rw [map_sum, Finset.sum_eq_single b]
  · rw [Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]
  · intro c _ hc
    rw [Derivation.map_smul, pderiv_X_of_ne hc, smul_zero]
  · intro h; exact absurd (Finset.mem_univ b) h

theorem pderiv_subst_linS [Fintype σ] (M : τ → σ → C) (b : τ) (H : MvPowerSeries σ C) :
    pderiv C b (subst (linS M) H) = ∑ w, M b w • subst (linS M) (pderiv C w H) := by
  rw [pderiv_subst (ordGE_linS M)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [pderiv_linS, smul_eq_C_mul]

end Lin

section Rows

variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']

theorem rename_subst_linS {σ τ τ' : Type} [Fintype σ] [Fintype τ] (f : τ ↪ τ') (M : τ → σ → C)
    (F : MvPowerSeries σ C) :
    rename f (subst (linS M) F) = subst (fun x => rename f (linS M x)) F := by
  rw [rename_eq_subst, subst_comp_subst_apply (hasSubst_linS M) (HasSubst.X_comp _)]
  congr 1
  funext x
  rw [rename_eq_subst]

end Rows

end Formalism.L2.FormalSeriesBounds
