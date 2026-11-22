import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.Mem.Top.TwChar

theorem addValuation_pos_iff_valuation_lt_one {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    0 < Examples₂.PlacesToy.valW w x ↔ w.valuation K x < 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : w.valuation K x ≠ 0 := by simpa using hx
  rw [Examples₂.PlacesToy.valW_of_ne w hx, vAdd, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.log_exp]
  norm_cast
  exact neg_pos

theorem addValuation_pos_iff_mem_asIdeal {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    0 < Examples₂.PlacesToy.valW w (x : K) ↔ x ∈ w.asIdeal := by
  rw [addValuation_pos_iff_valuation_lt_one, ← w.valuation_lt_one_iff_mem (K := K)]

theorem addVal_pos_iff {K : Type} [Field K] (v : AddValuation K (WithTop ℤ)) {x : K} (hx : x ≠ 0) :
    0 < v x ↔ ¬ 0 ≤ v x⁻¹ := by
  have h : v x + v x⁻¹ = 0 := by rw [← v.map_mul, mul_inv_cancel₀ hx, v.map_one]
  generalize v x = a at h
  generalize v x⁻¹ = b at h
  cases a with
  | top => simp at h
  | coe a =>
    cases b with
    | top => simp at h
    | coe b =>
      norm_cast at h ⊢
      omega

theorem overOne_plUnder (X : Stages) {B' : Base} (h : Enl X.B B') (v v' : B'.places.Pl)
    (hv : ∀ x ∈ B'.LL0, 0 ≤ B'.places.val v x ↔ 0 ≤ B'.places.val v' x) :
    OverOne X.toD7 (plUnder h v) (plUnder h v') := by
  intro x
  let y : 𝓞 X.B.LL := algebraMap (𝓞 ↥X.B.LL0) (𝓞 X.B.LL) x
  have key : ∀ u : B'.places.Pl, 0 < Examples₂.PlacesToy.valW (K := X.B.LL) (plUnder h u) (y : X.B.LL) ↔
      0 < Examples₂.PlacesToy.valW (K := B'.LL) u (incl h (y : X.B.LL)) := fun u =>
    (addValuation_pos_iff_mem_asIdeal _ y).trans ((mem_plUnder h u y).trans
      (addValuation_pos_iff_mem_asIdeal (K := B'.LL) u (RingOfIntegers.mapRingHom (incl h) y)).symm)
  have hm : incl h (y : X.B.LL) ∈ B'.LL0 := by
    have h1 : X.B.embLL (y : X.B.LL) ∈ B'.embLL '' ↑B'.LL0 := h.2.2.1 ▸ ⟨_, (x : ↥X.toD7.LL0).2, rfl⟩
    obtain ⟨z, hz, e⟩ := h1
    rw [← B'.embLL.injective (e.trans (embLL_incl h _).symm)]
    exact hz
  refine (key v).trans (Iff.trans ?_ (key v').symm)
  by_cases h0 : incl h (y : X.B.LL) = 0
  · rw [h0, AddValuation.map_zero, AddValuation.map_zero]
  · rw [addVal_pos_iff _ h0, addVal_pos_iff _ h0]
    exact not_congr (hv _ (B'.LL0.inv_mem hm))

theorem Seed.psiOk {D : D7} {A : D.ntw.Tw → Finset (PlE D.host)} (σ : Seed D A) {v : D.what₂.places.Pl} (hv : TwistedAt D v) :
    BlochKatoReduction.Gen.PsiOk (σ.s v) (A (σ.s v)) (σ.Q (σ.s v)) (σ.k (σ.s v)) (σ.ψ (σ.s v)) := by
  classical
  have h := ((σ.good v hv).2 1 (by simp)).1
  rw [zpow_one] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Finset.disjoint_union_right] at h2
  exact ⟨h1, by simp only [Finset.disjoint_union_right]; exact ⟨h2.1, h2.2.2⟩, h3⟩

end GlobalTheory.HeightCounting.Up

end
