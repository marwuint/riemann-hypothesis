import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

def AllClassesSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty),
    l.A = 1 → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty →
    ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), D'.p = D.p → D'.q = D.q →
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
        (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) →
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') →
      ∃ (i : Fin U.n) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La),
        (∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a') ∧
        ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
          ∃ e, gam (f l.M a) = U.t i a + l.M • e

namespace AllClasses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def SameMarking (l : Level H) {D D' : Datum H} (s t : D.La → D'.La) : Prop :=
  ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, s a = t a + l.M • e

def Occurs {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (U : FamilyUnif Xo σ ty) (D' : Datum H) (s : D.La → D'.La) : Prop :=
  ∃ (i : Fin U.n) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La),
    (∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a') ∧ SameMarking l (fun a => gam (s a)) (U.t i)

theorem exists_sign (n : ℕ) : ∃ s : ℤ, 0 < n → ((ordProj[2] n : ℕ) : ℤ) ∣ s - 1 ∧ ((ordCompl[2] n : ℕ) : ℤ) ∣ s + 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
  have hc : IsCoprime ((ordProj[2] n : ℕ) : ℤ) ((ordCompl[2] n : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_ordCompl Nat.prime_two hn.ne').pow_left _)
  obtain ⟨u, v, huv⟩ := hc
  exact ⟨v * (ordCompl[2] n : ℕ) - u * (ordProj[2] n : ℕ), fun _ =>
    ⟨⟨-2 * u, by linear_combination huv⟩, ⟨2 * v, by linear_combination -huv⟩⟩⟩

def sign (n : ℕ) : ℤ := (exists_sign n).choose

theorem sign_spec {n : ℕ} (hn : 0 < n) :
    ((ordProj[2] n : ℕ) : ℤ) ∣ sign n - 1 ∧ ((ordCompl[2] n : ℕ) : ℤ) ∣ sign n + 1 :=
  (exists_sign n).choose_spec hn

theorem dvd_sign_add_one {n : ℕ} (hn : Odd n) : (n : ℤ) ∣ sign n + 1 := by
  have h := (sign_spec hn.pos).2
  rwa [Nat.factorization_eq_zero_of_not_dvd (Odd.not_two_dvd_nat hn), pow_zero, Nat.div_one] at h

theorem exists_eq_add_nsmul {V : Type} [AddCommGroup V] {n : ℕ} {x y : ℤ} (h : (n : ℤ) ∣ x - y) (v : V) :
    ∃ e, x • v = y • v + n • e := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c • v, by rw [← natCast_zsmul, smul_smul, ← add_smul, ← hc, add_sub_cancel]⟩

theorem isTorsionFree (D : Datum H) : Module.IsTorsionFree (𝓞 E) D.La := by
  have := D.proj
  infer_instance

theorem exists_isTypeFn (H : Host E) (p q : ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
  have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
    rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
      (Equiv.sigmaSubtype τ))]
    simp
  exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem subsingleton_of_rank_zero (D : Datum H) (hD : D.p + D.q = 0) : Subsingleton D.La := by
  have := D.fin
  have := isTorsionFree D
  exact Module.finrank_zero_iff.mp (D.rank.trans hD)

theorem Occurs.twist {U : FamilyUnif Xo σ ty} {D' : Datum H} {f : ℕ → D.La →ₗ[𝓞 E] D'.La}
    (h : Occurs U D' (f l.M)) : Occurs U D' ((fun n => sign n • f n) l.M) := by
  obtain ⟨i, gam, h₁, h₂⟩ := h
  refine ⟨i, gam.trans (LinearEquiv.neg _), fun a a' => by simp [h₁], fun a ha => ?_⟩
  obtain ⟨e, he⟩ := h₂ a ha
  obtain ⟨e', he'⟩ := exists_eq_add_nsmul (x := sign l.M) (y := -1) (by simpa using dvd_sign_add_one l.odd)
    (gam (f l.M a))
  refine ⟨e - e', ?_⟩
  simp only [LinearMap.smul_apply, LinearEquiv.trans_apply, LinearEquiv.neg_apply, map_zsmul] at he ⊢
  rw [smul_neg, he', neg_one_zsmul, he, smul_sub]
  abel

end AllClasses

end GlobalTheory
