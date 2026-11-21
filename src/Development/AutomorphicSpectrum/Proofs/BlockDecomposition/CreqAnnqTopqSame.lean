import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient

open Finset
open scoped InnerProductSpace
open GlobalTheory.CompanionTheory.PairMult
open Formalism.REAL (GlRel KHighest)
open CompanionTheory.D.LK (Pos)
open CompanionTheory.RgExh.U (adC)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

noncomputable section

namespace GlobalTheory.CompanionTheory.PairMult.TopK

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    annq l x B = if l ∈ B then 0 else sgL l B • x (insert l B) := rfl

theorem creq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creq l x B = if l ∈ B then sgL l B • x (B.erase l) else 0 := rfl

theorem adC_diag_ne {p q : Fin n} (h : p ≠ q) (i : Pos n) : adC p q i i = 0 := by
  have h1 : ¬(q = i.1.1 ∧ i.1 = (p, i.1.2)) := fun e => h (by
    have := congrArg Prod.fst e.2
    exact (this.symm.trans e.1.symm))
  have h2 : ¬(i.1.2 = p ∧ i.1 = (i.1.1, q)) := fun e => h (by
    have := congrArg Prod.snd e.2
    exact e.1.symm.trans this)
  simp [adC, h1, h2]

theorem adC_diag_self (p : Fin n) (i : Pos n) :
    adC p p i i = (if i.1.1 = p then 1 else 0) - (if i.1.2 = p then 1 else 0) := by
  have e1 : (p = i.1.1 ∧ i.1 = (p, i.1.2)) ↔ i.1.1 = p :=
    ⟨fun h => h.1.symm, fun h => ⟨h.symm, Prod.ext h rfl⟩⟩
  have e2 : (i.1.2 = p ∧ i.1 = (i.1.1, p)) ↔ i.1.2 = p :=
    ⟨fun h => h.1, fun h => ⟨h, Prod.ext rfl h⟩⟩
  simp only [adC, e1, e2]

theorem sum_diag {lev : Fin n → ℕ} (hm : Monotone lev) (p : Fin n) :
    (∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC p p i i else 0) = ((2 * rhoU lev p : ℝ) : ℂ) := by
  have hs : ∀ i : Pos n, (if lev i.1.1 < lev i.1.2 then adC p p i i else 0) =
      (if lev i.1.1 < lev i.1.2 ∧ i.1.1 = p then (1 : ℂ) else 0) -
        (if lev i.1.1 < lev i.1.2 ∧ i.1.2 = p then (1 : ℂ) else 0) := by
    intro i
    rw [adC_diag_self]
    by_cases h : lev i.1.1 < lev i.1.2 <;> simp [h]
  have c1 : (univ.filter fun i : Pos n => lev i.1.1 < lev i.1.2 ∧ i.1.1 = p).card =
      (univ.filter fun b => lev p < lev b).card := by
    refine Finset.card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · intro i hi
      obtain ⟨h1, h2⟩ := (mem_filter.1 hi).2
      exact mem_filter.2 ⟨mem_univ _, h2 ▸ h1⟩
    · intro i hi j hj e
      have h1 := (mem_filter.1 hi).2.2
      have h2 := (mem_filter.1 hj).2.2
      exact Subtype.ext (Prod.ext (h1.trans h2.symm) e)
    · intro b hb
      have hb' := (mem_filter.1 hb).2
      exact ⟨⟨(p, b), hm.reflect_lt hb'⟩, mem_filter.2 ⟨mem_univ _, hb', rfl⟩, rfl⟩
  have c2 : (univ.filter fun i : Pos n => lev i.1.1 < lev i.1.2 ∧ i.1.2 = p).card =
      (univ.filter fun b => lev b < lev p).card := by
    refine Finset.card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · intro i hi
      obtain ⟨h1, h2⟩ := (mem_filter.1 hi).2
      exact mem_filter.2 ⟨mem_univ _, h2 ▸ h1⟩
    · intro i hi j hj e
      have h1 := (mem_filter.1 hi).2.2
      have h2 := (mem_filter.1 hj).2.2
      exact Subtype.ext (Prod.ext e (h1.trans h2.symm))
    · intro b hb
      have hb' := (mem_filter.1 hb).2
      exact ⟨⟨(b, p), hm.reflect_lt hb'⟩, mem_filter.2 ⟨mem_univ _, hb', rfl⟩, rfl⟩
  rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, c1, c2]
  simp only [rhoU]
  push_cast
  ring

end GlobalTheory.CompanionTheory.PairMult.TopK

namespace GlobalTheory.CompanionTheory.PairMult.TopK

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem rhoU_eq {lev : Fin n → ℕ} {a b : Fin n} (h : lev a = lev b) : rhoU lev a = rhoU lev b := by
  simp only [rhoU, h]

theorem kF_bracket {E1 E2 : Fin n → Fin n → Module.End ℂ V} (g1 : GlRel E1) (g2 : GlRel E2)
    (hc : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b) (p q : Fin n) :
    kF E1 E2 q p * kF E1 E2 p q - kF E1 E2 p q * kF E1 E2 q p = kF E1 E2 q q - kF E1 E2 p p := by
  have h1 := g1 q p p q
  have h2 := g2 q p p q
  simp only [if_true] at h1 h2
  have e : kF E1 E2 q p * kF E1 E2 p q - kF E1 E2 p q * kF E1 E2 q p =
      (E1 q p * E1 p q - E1 p q * E1 q p) + (E2 q p * E2 p q - E2 p q * E2 q p) := by
    simp only [kF, add_mul, mul_add, hc q p p q, hc p q q p]
    abel
  rw [e, h1, h2]
  simp only [kF]
  abel

theorem K_act {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hl : IsLev lam lev) {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hA : AdmFor lam lev E1 E2) {x : V} (hx : x ∈ hwSp E1 E2 (muQ lam lev)) {p q : Fin n} (hpq : lev p = lev q) :
    kF E1 E2 p q x = if p = q then ((muQ lam lev p : ℝ) : ℂ) • x else 0 := by
  have hK : KHighest (fun _ => true) (kF E1 E2) (muQ lam lev) x := hx
  rcases lt_trichotomy p q with h | rfl | h
  · rw [if_neg h.ne, hK.2 p q h rfl]
  · rw [if_pos rfl, hK.1 p]
  · rw [if_neg h.ne']
    have hmu : muQ lam lev q = muQ lam lev p := by
      simp only [muQ, rhoU_eq hpq.symm, hl.2 q p hpq.symm]
    have hb := LinearMap.congr_fun (kF_bracket hA.gl1 hA.gl2 hA.comm p q) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hK.2 q p h rfl, map_zero, sub_zero, hK.1 q, hK.1 p, hmu,
      sub_self] at hb
    have hn : ⟪kF E1 E2 p q x, kF E1 E2 p q x⟫_ℂ = 0 := by
      rw [hA.unitK p q x, hb, inner_zero_right]
    exact inner_self_eq_zero.1 hn

end GlobalTheory.CompanionTheory.PairMult.TopK
