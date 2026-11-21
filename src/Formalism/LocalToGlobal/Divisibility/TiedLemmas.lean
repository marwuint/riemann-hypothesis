import Mathlib
import Formalism.LocalToGlobal.Divisibility.RowSideTie

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

def PlConjEq (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ w, D.plEq (D.what₂.places.conj w) = conjPl (D.plEq w)

section PlConj

open Formalism.BasicNotions

theorem plConj_vAdd (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by
  by_cases hx : x = 0
  · subst hx
    simp [vAdd]
  · have h1 := D.conj_val w x
    rw [D.val_eq _ _ hx, D.val_eq _ _ (star_ne_zero.mpr hx)] at h1
    exact WithTop.coe_injective h1

theorem mem_iff_vAdd_pos {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    x ∈ w.asIdeal ↔ 0 < vAdd w (x : K) := by
  have hxK : (x : K) ≠ 0 := fun h => hx (RingOfIntegers.ext (by rw [h]; simp))
  have hv : w.valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hxK
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) w x]
  unfold vAdd
  rw [neg_pos]
  conv_rhs => rw [← WithZero.exp_lt_exp, WithZero.exp_log hv, WithZero.exp_zero]

theorem plConjEq (D : D7) : PlConjEq D := by
  unfold PlConjEq
  intro w
  have hc : ∀ y : 𝓞 D.what₂.LL, ((cO D.what₂.LL y : 𝓞 D.what₂.LL) : D.what₂.LL) = star (y : D.what₂.LL) :=
    fun y => rfl
  have hcc : ∀ y : 𝓞 D.what₂.LL, cO D.what₂.LL (cO D.what₂.LL y) = y := fun y =>
    RingOfIntegers.ext (by rw [hc, hc, star_star])
  ext x
  show x ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔ x ∈ (D.plEq w).asIdeal.map (cO D.what₂.LL)
  first
    | rw [Ideal.mem_map_of_equiv]
    | rw [Ideal.mem_map_iff_of_surjective _ (cO D.what₂.LL).surjective]
  have hiff : (∃ y ∈ (D.plEq w).asIdeal, cO D.what₂.LL y = x) ↔ cO D.what₂.LL x ∈ (D.plEq w).asIdeal := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [hcc]
    · intro h
      exact ⟨_, h, hcc x⟩
  rw [hiff]
  by_cases hx : x = 0
  · subst hx
    simp
  · have hne : cO D.what₂.LL x ≠ 0 := fun h => hx (by rw [← hcc x, h, map_zero])
    rw [mem_iff_vAdd_pos _ x hx, mem_iff_vAdd_pos _ _ hne, plConj_vAdd, hc]

end PlConj

section Fam

variable (D : Formalism.BasicNotions.D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (A : FamIn D.what₂.LL G Pl0 T m)

theorem ranks_r_sym (D : Formalism.BasicNotions.D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  have h1 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS
  omega

end Fam

end Formalism.L2.DIV
