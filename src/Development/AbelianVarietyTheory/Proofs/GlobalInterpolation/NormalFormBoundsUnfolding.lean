import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.normal_form_bounds_unfolding

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance GlobalTheory.Proof.NormalFormAtPrime

variable {E : Type} [Field E] [NumberField E]

theorem nonneg_of_intAt_zpow {P : HeightOneSpectrum (𝓞 E)} {k : ℤ} (h : IntAt P ((qOf P : E) ^ k)) : 0 ≤ k := by
  by_contra hk
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -((m + 1 : ℕ) : ℤ) := ⟨(-k - 1).toNat, by omega⟩
  subst hm
  obtain ⟨r, s, hs, e⟩ := h
  apply hs
  have hq := qOf_ne_zero P
  have e' : s = (qOf P : 𝓞 E) * ((qOf P : 𝓞 E) ^ m * r) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E _
    rw [map_mul, map_mul, map_pow, map_natCast, ← e, zpow_neg, zpow_natCast]
    field_simp
    ring
  rw [e']
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem le_of_zpow_eq {P : HeightOneSpectrum (𝓞 E)} {a b : ℤ} {u : E} (hu : IntAt P u)
    (h : (qOf P : E) ^ a = (qOf P : E) ^ b * u) : b ≤ a := by
  have hq := qOf_ne_zero P
  have : (qOf P : E) ^ (a - b) = u := by
    rw [zpow_sub₀ hq, h]
    field_simp
  have := nonneg_of_intAt_zpow (this ▸ hu)
  omega

variable [StarRing E] {n c : ℕ}

omit [NumberField E] [StarRing E] in
theorem inX_natAdd (x : Fin n → E) (b : Fin c) : Loc.inX E n c x (Fin.natAdd n b) = 0 := by
  rw [inX_apply, dif_neg (by simp)]

omit [NumberField E] [StarRing E] in
theorem atN_natAdd (v : Fin (n + c) → E) (b : Fin c) : Loc.atN v (n + b.1) = v (Fin.natAdd n b) := by
  unfold Loc.atN
  rw [dif_pos (by omega)]
  rfl

omit [NumberField E] [StarRing E] in
theorem nfGen_natAdd (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i b : Fin c) :
    nfGen q n c e z i (Fin.natAdd n b) = if b = i then (q : E) ^ e i else 0 := by
  unfold nfGen
  rw [Pi.smul_apply, Pi.add_apply]
  have h0 : (if i.1 = 0 then Loc.inX E n c z else 0 : Fin (n + c) → E) (Fin.natAdd n b) = 0 := by
    split_ifs
    · exact inX_natAdd _ _
    · rfl
  rw [h0]
  simp [Loc.eN, Fin.val_inj]

omit [NumberField E] [StarRing E] in
theorem nfGen_castAdd (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) (a : Fin n) :
    nfGen q n c e z i (Fin.castAdd c a) = if i.1 = 0 then (q : E) ^ e i * z a else 0 := by
  unfold nfGen
  rw [Pi.smul_apply, Pi.add_apply]
  have h0 : Loc.eN E (n + c) (n + i.1) (Fin.castAdd c a) = 0 := by
    unfold Loc.eN
    rw [if_neg (by have := a.2; simp; omega)]
  rw [h0]
  split_ifs
  · rw [inX_castAdd]; simp
  · simp

theorem coords_of_mem {P : HeightOneSpectrum (𝓞 E)} (hc : 1 ≤ c) {e : Fin c → ℤ} {z : Fin n → E} {y : Fin (n + c) → E}
    (hy : y ∈ nfLat P n c e z) :
    (∀ b, ∃ u, IntAt P u ∧ y (Fin.natAdd n b) = (qOf P : E) ^ e b * u) ∧
      ∀ a, IntAt P (y (Fin.castAdd c a) - y (Fin.natAdd n ⟨0, hc⟩) * z a) := by
  obtain ⟨l, hl, s, hs, rfl⟩ := hy
  have h1 : ∀ b, (Loc.inX E n c l + ∑ i, s i • nfGen (qOf P) n c e z i : Fin (n + c) → E) (Fin.natAdd n b) =
      (qOf P : E) ^ e b * s b := by
    intro b
    rw [Pi.add_apply, inX_natAdd, Finset.sum_apply]
    simp [nfGen_natAdd, mul_comm]
  refine ⟨fun b => ⟨s b, hs b, h1 b⟩, fun a => ?_⟩
  rw [h1, Pi.add_apply, inX_castAdd, Finset.sum_apply, Finset.sum_eq_single ⟨0, hc⟩]
  · rw [Pi.smul_apply, nfGen_castAdd, if_pos rfl, smul_eq_mul]
    convert (mem_stdAt_iff l).1 hl a using 1
    ring
  · intro b _ hb
    rw [Pi.smul_apply, nfGen_castAdd, if_neg (fun h => hb (Fin.ext h)), smul_zero]
  · simp

theorem nfGen_mem (P : HeightOneSpectrum (𝓞 E)) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) :
    nfGen (qOf P) n c e z i ∈ nfLat P n c e z :=
  ⟨0, zero_mem _, Pi.single i 1, intV_single P i, by simp [Pi.single_apply]⟩

omit [NumberField E] [StarRing E] in
theorem nfGen_mem_Ufl (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) :
    nfGen q n c e z i ∈ Loc.Ufl E n c (i.1 + 1) := by
  unfold nfGen
  refine Submodule.smul_mem _ _ (add_mem (eN_mem_Ufl (by omega)) ?_)
  split_ifs
  · exact inX_mem_Ufl _ _
  · exact zero_mem _

end GlobalTheory.Proof.normal_form_bounds_unfolding
