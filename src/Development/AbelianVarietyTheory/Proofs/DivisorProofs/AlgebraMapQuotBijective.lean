import Mathlib
open Polynomial

namespace GlobalTheory
namespace DedekindCodimG

end DedekindCodimG
end GlobalTheory

namespace GlobalTheory
namespace DedekindCodimG

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

private theorem isArtinianRing_quotient_of_ne_bot_of_isDedekindDomain (A : Type) [CommRing A] [IsDedekindDomain A]
    (I : Ideal A) (hI : I ≠ ⊥) : IsArtinianRing (A ⧸ I) := by
  have : Ring.KrullDimLE 0 (A ⧸ I) := by
    refine Ring.KrullDimLE.mk₀ fun Q hQ => ?_
    have hle : I ≤ Q.comap (Ideal.Quotient.mk I) := fun a ha => by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha, Q.zero_mem]
    have hne : Q.comap (Ideal.Quotient.mk I) ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hle))
    have hmax := (Ideal.IsPrime.comap (Ideal.Quotient.mk I) (hK := hQ)).isMaximal hne
    have := hmax.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hle)
    rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

private theorem module_finite_quotient_of_ne_bot_of_isDedekindDomain (k A : Type) [Field k] [CommRing A] [IsDedekindDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (I : Ideal A) (hI : I ≠ ⊥) :
    Module.Finite k (A ⧸ I) := by
  haveI := isArtinianRing_quotient_of_ne_bot_of_isDedekindDomain A I hI
  exact Module.finite_of_isArtinianRing k (A ⧸ I)

private theorem algebraMap_quotient_bijective_of_isMaximal_of_isAlgClosed (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsMaximal] :
    Function.Bijective (algebraMap k (A ⧸ P)) := by
  letI := Ideal.Quotient.field P
  haveI : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
  exact ⟨(algebraMap k (A ⧸ P)).injective, IsSepClosed.algebraMap_surjective k (A ⧸ P)⟩

private theorem mul_sup_span_singleton_eq_of_mem_of_not_mem_mul (A : Type) [CommRing A] [IsDedekindDomain A]
    (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsMaximal) (hP0 : P ≠ ⊥) {x : A} (hxI : x ∈ I)
    (hxIP : x ∉ I * P) : I * P ⊔ Ideal.span {x} = I := by
  have hle : I * P ⊔ Ideal.span {x} ≤ I :=
    sup_le (Ideal.mul_le_inf.trans inf_le_left) ((Ideal.span_singleton_le_iff_mem I).mpr hxI)
  obtain ⟨M, hM⟩ := Ideal.dvd_iff_le.mpr hle
  have hMP : M ∣ P := by
    have : I * M ∣ I * P := Ideal.dvd_iff_le.mpr (hM ▸ le_sup_left)
    exact (mul_dvd_mul_iff_left hI).mp this
  obtain ⟨N, hN⟩ := hMP
  rcases (Ideal.prime_of_isPrime hP0 hP.isPrime).irreducible.isUnit_or_isUnit hN with hu | hu
  · rw [hM, Ideal.isUnit_iff.mp hu, Ideal.mul_top]
  · rw [Ideal.isUnit_iff.mp hu, Ideal.mul_top] at hN
    subst hN
    refine absurd ?_ hxIP
    rw [← hM]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)

private theorem exists_sub_algebraMap_mem_of_isMaximal_of_isAlgClosed (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsMaximal] (r : A) :
    ∃ c : k, r - algebraMap k A c ∈ P := by
  obtain ⟨c, hc⟩ := (algebraMap_quotient_bijective_of_isMaximal_of_isAlgClosed k A P).2 (Ideal.Quotient.mk P r)
  refine ⟨c, Ideal.Quotient.eq.mp ?_⟩
  rw [Ideal.Quotient.mk_algebraMap, hc]

private theorem finrank_quotient_mul_maximal_eq_finrank_add_one (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (I P : Ideal A)
    (hI : I ≠ ⊥) (hP : P.IsMaximal) (hP0 : P ≠ ⊥) :
    Module.finrank k (A ⧸ I * P) = Module.finrank k (A ⧸ I) + 1 := by
  haveI := hP
  haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A (I * P) (mul_ne_zero hI hP0)
  haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A I hI
  obtain ⟨x, hxI, hxIP⟩ : ∃ x ∈ I, x ∉ I * P := by
    by_contra! h
    have hIP : I * P = I * ⊤ := by
      rw [Ideal.mul_top]
      exact le_antisymm (Ideal.mul_le_inf.trans inf_le_left) fun y hy => h y hy
    exact hP.ne_top (mul_left_cancel₀ hI hIP)
  let f : (A ⧸ I * P) →ₗ[k] (A ⧸ I) :=
    (Ideal.Quotient.factorₐ k (Ideal.mul_le_inf.trans inf_le_left : I * P ≤ I)).toLinearMap
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hker : LinearMap.ker f = k ∙ Ideal.Quotient.mk (I * P) x := by
    apply le_antisymm
    · intro z hz
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      have haI : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hz)
      rw [← mul_sup_span_singleton_eq_of_mem_of_not_mem_mul A I P hI hP hP0 hxI hxIP] at haI
      obtain ⟨b, hb, y, hy, rfl⟩ := Submodule.mem_sup.mp haI
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_of_isMaximal_of_isAlgClosed k A P r
      refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
      rw [← Ideal.Quotient.mkₐ_eq_mk k, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq,
        Algebra.smul_def]
      have h1 : x * (r - algebraMap k A c) ∈ I * P := Ideal.mul_mem_mul hxI hc
      have h2 : algebraMap k A c * x - (b + r * x) = -(b + x * (r - algebraMap k A c)) := by ring
      rw [h2]
      exact (I * P).neg_mem ((I * P).add_mem hb h1)
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hxI
  have hx0 : Ideal.Quotient.mk (I * P) x ≠ 0 := fun h => hxIP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, finrank_span_singleton hx0] at h
  exact h.symm

theorem _root_.GlobalTheory.DedekindCodimG.dedekind_finiteType_codim (k A : Type) [Field k]
    [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    (∀ (I : Ideal A), I ≠ ⊥ → Module.Finite k (A ⧸ I)) ∧
    (∀ (P : Ideal A), P.IsMaximal →
      Module.finrank k (A ⧸ P) = (1 : ℕ) ∧ ∃ (φ : A →ₐ[k] k), ∀ (u : A), u ∈ P ↔ (φ : A → k) u = (0 : k)) ∧
    (∀ (I J : Ideal A), I ≠ ⊥ → J ≠ ⊥ →
      Module.finrank k (A ⧸ I * J) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J)) ∧
    ∀ (I J : Ideal A), I ≠ ⊥ → I ≤ J → Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J) →
      I = J := by
  refine ⟨fun I hI => module_finite_quotient_of_ne_bot_of_isDedekindDomain k A I hI, ?_, ?_, ?_⟩
  · intro P hP
    haveI := hP
    let e : k ≃ₐ[k] A ⧸ P :=
      AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) (algebraMap_quotient_bijective_of_isMaximal_of_isAlgClosed k A P)
    refine ⟨by rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self],
      e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k P), fun u => ?_⟩
    change u ∈ P ↔ e.symm (Ideal.Quotient.mk P u) = 0
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  · intro I J hI hJ
    induction J using UniqueFactorizationMonoid.induction_on_prime generalizing I with
    | h₁ => exact absurd rfl hJ
    | h₂ u hu =>
      rw [Ideal.isUnit_iff.mp hu, Ideal.mul_top]
      haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [Module.finrank_zero_of_subsingleton (M := A ⧸ (⊤ : Ideal A)), add_zero]
    | h₃ a p ha hp ih =>
      have hp0 : p ≠ ⊥ := hp.ne_zero
      have hpmax : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp0
      have ha' : a ≠ ⊥ := ha
      rw [show I * (p * a) = I * a * p by ring, mul_comm p a,
        finrank_quotient_mul_maximal_eq_finrank_add_one k A (I * a) p (mul_ne_zero hI ha') hpmax hp0,
        finrank_quotient_mul_maximal_eq_finrank_add_one k A a p ha' hpmax hp0, ih I hI ha']
      ring
  · intro I J hI hIJ hle
    have hJ : J ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hIJ))
    haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A I hI
    haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A J hJ
    let f : (A ⧸ I) →ₗ[k] (A ⧸ J) := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk _ a, rfl⟩
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
    have hker : LinearMap.ker f = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    refine le_antisymm hIJ fun a ha => ?_
    have hmem : Ideal.Quotient.mk I a ∈ LinearMap.ker f :=
      LinearMap.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
    rw [hker, Submodule.mem_bot] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

end DedekindCodimG
end GlobalTheory
