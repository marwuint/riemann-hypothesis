import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob

noncomputable section

namespace UpperTheory.V.Af

theorem finite_image_of_card_le {P Y : Type} (Sig : Set P) (Iso : P → P → Prop) (f : P → Y)
    (hiso : ∀ a ∈ Sig, ∀ b ∈ Sig, Iso a b → f a = f b) (N : ℕ)
    (hcard : ∀ S : Finset P, (∀ a ∈ S, a ∈ Sig) → (∀ a ∈ S, ∀ b ∈ S, Iso a b → a = b) → S.card ≤ N) :
    Finite ↥(f '' Sig) ∧ Nat.card ↥(f '' Sig) ≤ N := by
  classical
  have key : ∀ T : Finset Y, (↑T : Set Y) ⊆ f '' Sig → T.card ≤ N := by
    intro T hT
    have hpre : ∀ y : T, ∃ a, a ∈ Sig ∧ f a = y.1 := fun y => hT y.2
    choose g hgS hgf using hpre
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      rw [← hgf x, ← hgf y, hxy]
    have hS := hcard (Finset.univ.image g) ?_ ?_
    · rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe] at hS
    · intro a ha
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp ha
      exact hgS y
    · intro a ha b hb hab
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hb
      have hxy := hiso _ (hgS x) _ (hgS y) hab
      rw [hgf x, hgf y] at hxy
      rw [Subtype.ext hxy]
  have hfin : (f '' Sig).Finite := by
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (N + 1)
    have := key t ht
    omega
  refine ⟨hfin.to_subtype, ?_⟩
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  exact key _ (by simp)

open NumberField IsDedekindDomain in

theorem natCast_notMem_of_not_dvd {F : Type} [Field F] [NumberField F] {p M : ℕ} (hp : p.Prime)
    {w : HeightOneSpectrum (𝓞 F)} (hw : (p : 𝓞 F) ∈ w.asIdeal) (hM : ¬ p ∣ M) : (M : 𝓞 F) ∉ w.asIdeal := by
  intro hMw
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr hM
  have h := Nat.gcd_eq_gcd_ab p M
  rw [Nat.Coprime.gcd_eq_one hcop] at h
  have h1 : (1 : 𝓞 F) = (p : 𝓞 F) * (Nat.gcdA p M : 𝓞 F) + (M : 𝓞 F) * (Nat.gcdB p M : 𝓞 F) := by
    have h' := congrArg (Int.cast : ℤ → 𝓞 F) h
    push_cast at h'
    exact h'
  have hone : (1 : 𝓞 F) ∈ w.asIdeal := by
    rw [h1]
    exact w.asIdeal.add_mem (Ideal.mul_mem_right _ _ hw) (Ideal.mul_mem_right _ _ hMw)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

open NumberField IsDedekindDomain in

theorem eventually_natCast_notMem {F : Type} [Field F] [NumberField F] {M : ℕ} (hM : M ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (M : 𝓞 F) ∉ w.asIdeal := by
  rw [Filter.eventually_cofinite]
  have hM' : (M : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hI : Ideal.span {(M : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hM'
  refine (Ideal.finite_factors hI).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq, not_not] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hw

end UpperTheory.V.Af
