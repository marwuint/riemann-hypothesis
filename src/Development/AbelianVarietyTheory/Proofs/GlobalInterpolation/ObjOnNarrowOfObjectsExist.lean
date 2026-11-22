import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.FewBadPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRefill

noncomputable section

namespace GlobalTheory.ObjExCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory NumberField GlobalTheory.EX GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

variable {R : Ranks}

theorem one_lt_condE (H : Host R) : 1 < condE H := by
  unfold condE
  exact lt_of_lt_of_le H.hyp.2.1.one_lt (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))

theorem norm_modEq (H : Host R) (π : 𝓞 H.E) {T N : ℕ} (hN : N ≠ 0)
    (hn : (π : H.E) * H.conj (π : H.E) = (T : H.E)) (h1 : π - 1 ∈ Ideal.span {((N : ℕ) : 𝓞 H.E)}) :
    T ≡ 1 [MOD N] := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  have hyi : IsIntegral ℤ (a : H.E) := RingOfIntegers.isIntegral_coe a
  have hπ : (π : H.E) = 1 + N * (a : H.E) := by
    have := congrArg (fun z : 𝓞 H.E => (z : H.E)) ha
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    linear_combination -this
  have hci : IsIntegral ℤ (H.conj (a : H.E)) := hyi.map ((H.conj : H.E →+* H.E).toIntAlgHom)
  rw [hπ, map_add, map_mul, map_one, map_natCast] at hn
  set z : H.E := a + H.conj (a : H.E) + N * (a * H.conj (a : H.E)) with hz
  have hzi : IsIntegral ℤ z :=
    (hyi.add hci).add ((isIntegral_natCast (R := ℤ) (B := H.E) N).mul (hyi.mul hci))
  have hM0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have h4 : z = algebraMap ℚ H.E (((T : ℚ) - 1) / N) := by
    have hM0' : (N : H.E) ≠ 0 := by exact_mod_cast hN
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, eq_div_iff hM0', hz]
    linear_combination hn
  rw [h4, isIntegral_algebraMap_iff (algebraMap ℚ H.E).injective] at hzi
  obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi
  have h5 : (((T : ℤ) - ((1 : ℕ) : ℤ) : ℤ) : ℚ) = ((N * n : ℤ) : ℚ) := by
    have : (n : ℚ) = ((T : ℚ) - 1) / N := by simpa using hn'
    push_cast
    rw [this]
    field_simp
  exact (Nat.modEq_iff_dvd.2 ⟨n, by exact_mod_cast h5⟩).symm

theorem T_modEq (D : D7) (u : D.what₂.Word) : (D.mem u).A.T ≡ 1 [MOD condE D.host] := by
  obtain ⟨π, -, h2, h3⟩ := D.T_norm u
  have h0 : condE D.host * (D.host.g 0 * D.host.g 1) ^ 2 ≠ 0 :=
    Nat.mul_ne_zero (by have := one_lt_condE D.host; omega)
      (pow_ne_zero _ (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  exact (norm_modEq D.host π h0 h2 h3).of_mul_right _

def LeastPrimeCong (H : Host R) (q0 : ℕ) : Prop :=
  ∃ r' : ℕ, IsLeast {l : ℕ | l.Prime ∧ ¬ l ∣ condE H * (H.pde - 1) * (H.pde' - 1)} r' ∧ q0 ≡ 1 [MOD r' * condE H]

def BsCanon {C : FC} (p : Pt C) : Prop := ∀ h t, p.ta.Gx.bs h t = Arith.bsH h t

def Common (Q : PtProp) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 c6 Cb : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ Cdg x0 : ℝ,
      ∀ (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ) (M : ℕ)
        (c : Fin M → Fin (R.k - 2) → Bool), s.eps = eps → x0 ≤ s.x → RankVal s R → H.CT2 = C.CT2 →
        HostGood s C8 4 c6 Cb H q0 → LeastPrimeCong H q0 → WinOK s C.GK H a b →
        M = ⌈3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊ → Function.Injective c →
        ∃ off : ℕ → ℕ → ℝ, ∀ u0 < R.n,
        ∃ p : Pt C, p.L.sc = s ∧ Val C cD ch p.L ∧ HostArith p.D.host ∧ p.From H a b c u0 ∧ BsCanon p ∧
          (∀ (j : ℕ) (t : G.HH p.D), p.ta.Gx.off j (false, t) = off j t.val) ∧ p.Has Q ∧
          ChProviso_at p.L 3 ∧ p.L.TuGe ∧ (∀ u, Real.log ((p.D.mem u).A.T : ℝ) ≤ C.CTu * p.D.R.m * p.L.sc.L) ∧
          FactDGam p.D Cdg

theorem Common.imp {Q Q' : PtProp} (h : Common Q) (hQ : ∀ (C : FC) (p : Pt C), p.Has Q → p.Has Q') : Common Q' := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 c6 Cb h1 h2 h3 h4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 c6 Cb h1 h2 h3 h4
  refine ⟨K0, fun C hC h8 hL => ?_⟩
  obtain ⟨c1, h⟩ := h C hC h8 hL
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨Cdg, x0, h⟩ := h ch hch
  refine ⟨Cdg, x0, fun s R H q0 a b M c hs hx hR hT hH hr hw hM hc => ?_⟩
  obtain ⟨off, h⟩ := h s R H q0 a b M c hs hx hR hT hH hr hw hM hc
  refine ⟨off, fun u0 hu => ?_⟩
  obtain ⟨p, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h u0 hu
  exact ⟨p, a1, a2, a3, a4, a5, a6, hQ C p a7, a8⟩

end GlobalTheory.ObjExCompare

end
