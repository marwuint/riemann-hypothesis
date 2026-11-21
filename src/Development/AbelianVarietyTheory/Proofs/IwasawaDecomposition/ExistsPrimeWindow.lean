import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralBinomLePowCardPrimesBetween

noncomputable section
open Polynomial Formalism.CyclotomicNorms

namespace GlobalTheory.MemN.GoodEx

theorem pow_primeToPart {M : Type*} [Monoid M] {l : ℕ} (hl : l.Prime) {x : M} (hx : IsOfFinOrder x) :
    ∃ a, primeToPart l x ^ l ^ a = x ^ l ^ a := by
  refine ⟨(orderOf x).factorization l, ?_⟩
  unfold primeToPart
  set n := orderOf x with hn
  set A := l ^ n.factorization l with hA
  have hn0 : n ≠ 0 := hx.orderOf_pos.ne'
  have hAm : A * (n / A) = n := Nat.ordProj_mul_ordCompl_eq_self n l
  have hcop : Nat.Coprime A (n / A) := (Nat.coprime_ordCompl hl hn0).pow_left _
  have h1 : A * ((A : ZMod (n / A))⁻¹).val ≡ 1 [MOD n / A] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_one]
    exact ZMod.mul_val_inv hcop
  rw [← pow_mul, hx.pow_eq_pow_iff_modEq, ← hn]
  have h2 := h1.mul_left' A
  rw [hAm, mul_one] at h2
  rwa [mul_comm]

theorem exists_pow_eq {M : Type*} [Monoid M] {l : ℕ} (hl : l.Prime) {x y : M} (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) (h : primeToPart l x = primeToPart l y) : ∃ s, x ^ l ^ s = y ^ l ^ s := by
  obtain ⟨a, ha⟩ := pow_primeToPart hl hx
  obtain ⟨b, hb⟩ := pow_primeToPart hl hy
  refine ⟨a + b, ?_⟩
  rw [pow_add, pow_mul, ← ha, h, ← pow_mul, mul_comm, pow_mul, hb, ← pow_mul]

variable {g : ℕ} [Fact g.Prime]

theorem frob_inj (i : ℕ) {x y : Fbar g} (h : x ^ g ^ i = y ^ g ^ i) : x = y := by
  obtain ⟨f, hf⟩ := GlobalTheory.CuspGL.exists_algHom_pow_card_pow (F := ZMod g) i
  apply f.injective
  show f _ = f _
  rw [hf, hf, Nat.card_zmod, h]

theorem pow_deg (x : Fbar g) : x ^ g ^ (minpoly (ZMod g) x).natDegree = x := by
  simpa [Nat.card_zmod] using (GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow (F := ZMod g) x _).1 dvd_rfl

theorem finOrder {x : Fbar g} (hx : x ≠ 0) : IsOfFinOrder x := by
  have h := pow_deg x
  have h1 : 1 < g ^ (minpoly (ZMod g) x).natDegree :=
    Nat.one_lt_pow (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne' (Fact.out : g.Prime).one_lt
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨g ^ (minpoly (ZMod g) x).natDegree - 1, by omega, ?_⟩
  apply mul_right_cancel₀ hx
  rw [← pow_succ, Nat.sub_add_cancel h1.le, h, one_mul]

theorem mem_roots_minpoly {x y : Fbar g} (h : y ∈ rootsBar (minpoly (ZMod g) x)) :
    ∃ i, i < (minpoly (ZMod g) x).natDegree ∧ y = x ^ g ^ i := by
  unfold rootsBar at h
  rw [GlobalTheory.CuspGL.roots_minpoly_eq_map_range (F := ZMod g) x, Nat.card_zmod] at h
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 h
  exact ⟨i, Multiset.mem_range.1 hi, rfl⟩

def Gen (d : ℕ) (T : Finset (ZMod g)ˣ) (x : Fbar g) : Prop :=
  x ≠ 0 ∧ (minpoly (ZMod g) x).natDegree = d ∧
    (∀ l s a : ℕ, l.Prime → 0 < a → a < d → (x ^ l ^ s) ^ g ^ a = x ^ l ^ s → Exc g d l) ∧
    ∀ l s : ℕ, l.Prime → ∀ t ∈ T, x ^ l ^ s ≠ algebraMap (ZMod g) (Fbar g) (t : ZMod g) ^ l ^ s

theorem Gen.root_ne {d : ℕ} {T : Finset (ZMod g)ˣ} {x y : Fbar g} (h : Gen d T x)
    (hy : y ∈ rootsBar (minpoly (ZMod g) x)) : y ≠ 0 := by
  obtain ⟨i, -, rfl⟩ := mem_roots_minpoly hy
  exact pow_ne_zero _ h.1

theorem Gen.exc {d : ℕ} {T : Finset (ZMod g)ˣ} {x y : Fbar g} (h : Gen d T x) {l s a : ℕ} (hl : l.Prime)
    (hy : y ∈ rootsBar (minpoly (ZMod g) x)) (ha : 0 < a) (had : a < d) (he : (y ^ l ^ s) ^ g ^ a = y ^ l ^ s) :
    Exc g d l := by
  obtain ⟨i, -, rfl⟩ := mem_roots_minpoly hy
  refine h.2.2.1 l s a hl ha had (frob_inj i ?_)
  rw [pow_right_comm (x ^ l ^ s), pow_right_comm x (l ^ s), he]

theorem Gen.apart {d : ℕ} {T : Finset (ZMod g)ˣ} {x y z : Fbar g} (h : Gen d T x) {l : ℕ} (hl : l.Prime)
    (hn : ¬ Exc g d l) (hy : y ∈ rootsBar (minpoly (ZMod g) x)) (hz : z ∈ rootsBar (minpoly (ZMod g) x))
    (he : primeToPart l y = primeToPart l z) : y = z := by
  obtain ⟨s, hs⟩ := exists_pow_eq hl (finOrder (h.root_ne hy)) (finOrder (h.root_ne hz)) he
  clear he
  obtain ⟨i, hi, hyi⟩ := mem_roots_minpoly hy
  obtain ⟨j, hj, hzj⟩ := mem_roots_minpoly hz
  rw [h.2.1] at hi hj
  wlog hij : i ≤ j generalizing y z i j
  · exact (this hz hy hs.symm j hj hzj i hi hyi (by omega)).symm
  rcases hij.eq_or_lt with rfl | hij
  · rw [hyi, hzj]
  · refine absurd (h.exc (s := s) (a := j - i) hl hy (by omega) (by omega) ?_) hn
    rw [pow_right_comm, hs, hyi, hzj, ← pow_mul x, ← pow_add, Nat.add_sub_cancel' hij.le]

end GlobalTheory.MemN.GoodEx

namespace GlobalTheory.MemN
end GlobalTheory.MemN
