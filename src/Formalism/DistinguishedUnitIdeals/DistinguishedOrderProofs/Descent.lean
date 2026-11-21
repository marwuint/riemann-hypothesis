import Mathlib
import Formalism.DistinguishedUnitIdeals.UnivPart

noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

section Helpers

variable {O : Type} [CommRing O]

theorem algHom_C (φ : PowerSeries O →ₐ[O] PowerSeries O) (a : O) : φ (C a) = C a := by
  simpa [PowerSeries.algebraMap_apply] using φ.commutes a

theorem algHom_eq_const_add (φ : PowerSeries O →ₐ[O] PowerSeries O) (h : PowerSeries O) :
    φ h = C (constantCoeff h) + φ X * φ (mk fun p => coeff (p + 1) h) := by
  conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const h]
  rw [map_add, map_mul, algHom_C]
  ring

theorem order_map_toNat_of_isDistinguishedAt {I : Ideal O} (hI : I ≠ ⊤) {E : Polynomial O}
    (hE : E.IsDistinguishedAt I) :
    ((E : PowerSeries O).map (Ideal.Quotient.mk I)).order.toNat = E.natDegree := by
  have h := hE.coe_natDegree_eq_order_map (E : PowerSeries O) 1
    (by rw [map_one]; exact (Ideal.ne_top_iff_one I).mp hI) (by rw [mul_one])
  rw [← h, ENat.toNat_coe]

theorem exists_div_of_isDistinguishedAt {I : Ideal O} [IsAdicComplete I O] (hI : I ≠ ⊤)
    {E : Polynomial O} (hE : E.IsDistinguishedAt I) (F : PowerSeries O) :
    ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < E.natDegree ∧
      F = (E : PowerSeries O) * q + r := by
  have H := hE.isWeierstrassDivisorAt hI
  have hd := H.isWeierstrassDivisionAt_div_mod F
  refine ⟨H.div F, H.mod F, ?_, hd.eq_mul_add⟩
  have h1 := hd.degree_lt
  rwa [order_map_toNat_of_isDistinguishedAt hI hE] at h1

theorem eq_zero_of_isDistinguishedAt_mul {I : Ideal O} [IsAdicComplete I O] (hI : I ≠ ⊤)
    {E : Polynomial O} (hE : E.IsDistinguishedAt I) {q : PowerSeries O} {r : Polynomial O}
    (hr : r.degree < E.natDegree) (h : (E : PowerSeries O) * q = r) : r = 0 := by
  have H := hE.isWeierstrassDivisorAt hI
  refine (H.eq_zero_of_mul_eq ?_ h).2
  rwa [order_map_toNat_of_isDistinguishedAt hI hE]

theorem coe_sum_fin {d : ℕ} (a : Fin d → O) :
    ((∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O) :
      PowerSeries O) = ∑ i : Fin d, C (a i) * X ^ (i : ℕ) := by
  have h := map_sum (Polynomial.coeToPowerSeries.ringHom (R := O))
    (fun i : Fin d => Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) Finset.univ
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_pow, Polynomial.coe_X] at h
  exact h

theorem coeff_sum_fin {d : ℕ} (a : Fin d → O) (j : Fin d) :
    (∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O).coeff j = a j := by
  simp [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj]

theorem coe_eq_sum_fin {d : ℕ} {r : Polynomial O} (hr : r.degree < d) :
    (r : PowerSeries O) = ∑ i : Fin d, C (r.coeff i) * X ^ (i : ℕ) := by
  have h : r = ∑ i : Fin d, Polynomial.C (r.coeff i) * Polynomial.X ^ (i : ℕ) := by
    ext j
    rw [Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    by_cases hj : j < d
    · rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext h.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hr (by exact_mod_cast not_lt.mp hj))]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro h
      exact hj (h ▸ i.2)
  rw [← coe_sum_fin]
  exact congrArg _ h

theorem eq_zero_of_forall_pow_dvd {R : Type} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {P : R} (hP : ¬ IsUnit P) {x : R} (h : ∀ N : ℕ, P ^ N ∣ x) : x = 0 := by
  have hI : Ideal.span {P} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  have h0 := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  have hx : x ∈ ⨅ i, Ideal.span {P} ^ i := Ideal.mem_iInf.mpr fun N => by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h N
  rw [h0, Ideal.mem_bot] at hx
  exact hx

theorem exists_sum_algHom_mul_X_pow (φ : PowerSeries O →ₐ[O] PowerSeries O) (d : ℕ)
    (hdiv : ∀ F : PowerSeries O, ∃ (q : PowerSeries O) (r : Polynomial O),
      r.degree < d ∧ F = φ X * q + r)
    (hkrull : ∀ x : PowerSeries O, (∀ N : ℕ, φ X ^ N ∣ x) → x = 0)
    (F : PowerSeries O) : ∃ h : Fin d → PowerSeries O, F = ∑ i, φ (h i) * X ^ (i : ℕ) := by
  choose qf rf hrf hF using hdiv
  let H : PowerSeries O → Fin d → PowerSeries O := fun F i => mk fun k => (rf (qf^[k] F)).coeff i
  have hT : ∀ G i, (mk fun p => coeff (p + 1) (H G i)) = H (qf G) i := by
    intro G i
    ext p
    simp [H, PowerSeries.coeff_mk, Function.iterate_succ_apply]
  have hc : ∀ G i, constantCoeff (H G i) = (rf G).coeff i := by
    intro G i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    rfl
  have hS : ∀ G, ∑ i, φ (H G i) * X ^ (i : ℕ) = rf G + φ X * ∑ i, φ (H (qf G) i) * X ^ (i : ℕ) := by
    intro G
    rw [coe_eq_sum_fin (hrf G), Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algHom_eq_const_add φ (H G i), hc, hT]
    ring
  have hdvd : ∀ N G, φ X ^ N ∣ G - ∑ i, φ (H G i) * X ^ (i : ℕ) := by
    intro N
    induction N with
    | zero => intro G; simp
    | succ N ih =>
      intro G
      obtain ⟨c, hc'⟩ := ih (qf G)
      refine ⟨c, ?_⟩
      rw [hS G]
      linear_combination (hF G) + φ X * hc'
  refine ⟨H F, ?_⟩
  exact (sub_eq_zero.mp (hkrull _ fun N => hdvd N F))

theorem eq_zero_of_sum_algHom_mul_X_pow [IsDomain O] (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (d : ℕ)
    (huniq : ∀ (a : Fin d → O) (q : PowerSeries O),
      ∑ i, C (a i) * X ^ (i : ℕ) = φ X * q → ∀ i, a i = 0)
    (hP0 : φ X ≠ 0) :
    ∀ (n : ℕ) (h : Fin d → PowerSeries O), ∑ i, φ (h i) * X ^ (i : ℕ) = 0 →
      ∀ i, coeff n (h i) = 0 := by
  have step : ∀ h : Fin d → PowerSeries O, ∑ i, φ (h i) * X ^ (i : ℕ) = 0 →
      (∀ i, constantCoeff (h i) = 0) ∧
        ∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ) = 0 := by
    intro h hs
    have e : ∑ i, φ (h i) * X ^ (i : ℕ) = ∑ i, C (constantCoeff (h i)) * X ^ (i : ℕ) +
        φ X * ∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [algHom_eq_const_add φ (h i)]
      ring
    rw [hs] at e
    have h0 := huniq (fun i => constantCoeff (h i))
      (-(∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ))) (by linear_combination -e)
    refine ⟨h0, ?_⟩
    have hsum0 : ∑ i, C (constantCoeff (h i)) * X ^ (i : ℕ) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [show constantCoeff (h i) = 0 from h0 i, map_zero, zero_mul]
    rw [hsum0, zero_add] at e
    exact (mul_eq_zero.mp e.symm).resolve_left hP0
  intro n
  induction n with
  | zero =>
    intro h hs i
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (step h hs).1 i
  | succ n ih =>
    intro h hs i
    have h1 := ih _ (step h hs).2 i
    simpa [PowerSeries.coeff_mk] using h1

end Helpers

end Formalism.ExponentWindows
