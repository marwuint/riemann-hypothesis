import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureCballZpow

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical

namespace GlobalTheory.CompanionTheory.IwJac.StepIdx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem val_lt_one {ϖ : kˣ} (h : ord k ϖ = 1) : valuation k (ϖ : k) < 1 := by
  have h1 : ¬ valuation k ((1 : kˣ) : k) ≤ valuation k (ϖ : k) := by
    rw [GlobalTheory.OrdShellInt.val_le_iff_ord, ord_eq_zero (x := (1 : kˣ)) (by simp)]; omega
  simpa using h1

def om (ϖ : kˣ) (h : ord k ϖ = 1) : 𝒪[k] := ⟨ϖ, (val_lt_one h).le⟩

theorem om_pow_dvd_iff {ϖ : kˣ} (h : ord k ϖ = 1) (a : 𝒪[k]) (m : ℕ) :
    om ϖ h ^ m ∣ a ↔ valuation k (a : k) ≤ valuation k ((ϖ : k) ^ m) := by
  refine ((Valuation.integer.integers (valuation k)).dvd_iff_le).trans ?_
  simp only [map_pow]
  rfl

def ent (g : GL (Fin n) k) (i j : Fin n) : 𝒪[k] :=
  if h : valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 then ⟨_, h⟩ else 0

theorem nO_int {g : GL (Fin n) k} (hg : g ∈ nO k n) (i j : Fin n) :
    valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  obtain ⟨⟨h, rfl⟩, -⟩ := mem_iwahori.1 hg.1
  exact ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j).2

theorem ent_coe {g : GL (Fin n) k} (hg : g ∈ nO k n) (i j : Fin n) :
    (ent g i j : k) = (g : Matrix (Fin n) (Fin n) k) i j := by
  simp [ent, nO_int hg]

theorem mul_entry {ϖ : kˣ} {x : Fin n → ℤ} {d : ℕ} {g h : GL (Fin n) k} (hg : g ∈ filt ϖ x d)
    (hh : h ∈ filt ϖ x d) {i j : Fin n} (hij : j.val = i.val + (d + 1)) :
    valuation k (((g * h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - (g : Matrix (Fin n) (Fin n) k) i j
        - (h : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k (((ϖ ^ (x i - x j) : kˣ)) : k) := by
  obtain ⟨hgO, dg, -⟩ := mem_filt.1 hg
  obtain ⟨hhO, dh, -⟩ := mem_filt.1 hh
  obtain ⟨g0, g1⟩ := (mem_unipB k).1 hgO.2
  obtain ⟨h0, h1⟩ := (mem_unipB k).1 hhO.2
  have hne : i ≠ j := by intro e; rw [e] at hij; omega
  have e : ((g * h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - (g : Matrix (Fin n) (Fin n) k) i j
        - (h : Matrix (Fin n) (Fin n) k) i j =
      ∑ l, ((g : Matrix (Fin n) (Fin n) k) i l * (h : Matrix (Fin n) (Fin n) k) l j
        - (if l = j then (g : Matrix (Fin n) (Fin n) k) i j else 0)
        - (if l = i then (h : Matrix (Fin n) (Fin n) k) i j else 0)) := by
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp
  rw [e]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rcases lt_trichotomy l i with hl | rfl | hl
  · have a1 : l ≠ i := hl.ne
    have a2 : l ≠ j := by intro e; rw [e] at hl; have := Fin.lt_def.1 hl; omega
    rw [g0 i l hl, if_neg a1, if_neg a2]; simp
  · rw [g1, if_pos rfl, if_neg hne]; simp
  rcases lt_trichotomy l j with hl' | rfl | hl'
  · rw [if_neg hl.ne', if_neg hl'.ne, sub_zero, sub_zero, map_mul]
    have e : (((ϖ ^ (x i - x j) : kˣ)) : k) = ((ϖ ^ (x i - x l) : kˣ) : k) * ((ϖ ^ (x l - x j) : kˣ) : k) := by
      rw [← Units.val_mul, ← _root_.zpow_add]; congr 2; ring
    rw [e, map_mul]
    exact mul_le_mul' (dg _ _ hl (by have := Fin.lt_def.1 hl'; omega))
      (dh _ _ hl' (by have := Fin.lt_def.1 hl; omega))
  · rw [h1, if_pos rfl, if_neg hl.ne']; simp
  · have a2 : l ≠ j := hl'.ne'
    rw [h0 l j hl', if_neg hl.ne', if_neg a2]; simp

def tr0 (c : 𝒪[k]) (i j : Fin n) (hij : i ≠ j) : GL (Fin n) 𝒪[k] :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same _ _ hij]; simp,
    by rw [transvection_mul_transvection_same _ _ hij]; simp⟩

theorem coe_zpow_eq {ϖ : kˣ} {e : ℤ} (he : 0 ≤ e) : (((ϖ ^ e : kˣ)) : k) = (ϖ : k) ^ e.toNat := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le he
  simp

theorem mem_span_iff {ϖ : kˣ} (h : ord k ϖ = 1) (a : 𝒪[k]) {e : ℤ} (he : 0 ≤ e) :
    a ∈ Ideal.span {om ϖ h ^ e.toNat} ↔ valuation k (a : k) ≤ valuation k (((ϖ ^ e : kˣ)) : k) := by
  rw [Ideal.mem_span_singleton, om_pow_dvd_iff, coe_zpow_eq he]

abbrev AQ (ϖ : kˣ) (h : ord k ϖ = 1) (x : Fin n → ℤ) (p : Fin n × Fin n) : Type :=
  𝒪[k] ⧸ Ideal.span {om ϖ h ^ (x p.1 - x p.2).toNat}

theorem pair_lt {d : ℕ} (p : diagPairs n d) : p.1.1 < p.1.2 := by
  have := (Finset.mem_filter.1 p.2).2
  exact Fin.lt_def.2 (by omega)

theorem pair_eq {d : ℕ} (p : diagPairs n d) : p.1.2.val = p.1.1.val + (d + 1) :=
  (Finset.mem_filter.1 p.2).2

theorem pair_nonneg {x : Fin n → ℤ} (hx : StrictAnti x) {d : ℕ} (p : diagPairs n d) :
    0 ≤ x p.1.1 - x p.1.2 :=
  sub_nonneg.2 (hx (pair_lt p)).le

def phi {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) :
    filt ϖ x d →* Multiplicative (∀ p : diagPairs n d, AQ ϖ h x p.1) :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd fun p => Ideal.Quotient.mk _ (ent g.1 p.1.1 p.1.2)) fun g g' => by
    rw [← ofAdd_add]
    congr 1
    funext p
    rw [Pi.add_apply, ← map_add, Ideal.Quotient.eq, mem_span_iff h _ (pair_nonneg hx p)]
    have e := mul_entry g.2 g'.2 (pair_eq p)
    have hO : g.1 * g'.1 ∈ nO k n := mul_mem g.2.1 g'.2.1
    have e2 : ((ent (g.1 * g'.1) p.1.1 p.1.2 - (ent g.1 p.1.1 p.1.2 + ent g'.1 p.1.1 p.1.2) : 𝒪[k]) : k) =
        ((g.1 * g'.1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p.1.1 p.1.2
          - (g.1 : Matrix (Fin n) (Fin n) k) p.1.1 p.1.2 - (g'.1 : Matrix (Fin n) (Fin n) k) p.1.1 p.1.2 := by
      show (ent (g.1 * g'.1) p.1.1 p.1.2 : k) - ((ent g.1 p.1.1 p.1.2 : k) + (ent g'.1 p.1.1 p.1.2 : k)) = _
      rw [ent_coe hO, ent_coe g.2.1, ent_coe g'.2.1]
      ring
    show valuation k ((ent (g.1 * g'.1) p.1.1 p.1.2 - (ent g.1 p.1.1 p.1.2 + ent g'.1 p.1.1 p.1.2) : 𝒪[k]) : k) ≤ _
    rw [e2]
    exact e

theorem phi_apply {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) (g : filt ϖ x d) :
    phi h hx d g = Multiplicative.ofAdd fun p => Ideal.Quotient.mk _ (ent g.1 p.1.1 p.1.2) := rfl

end GlobalTheory.CompanionTheory.IwJac.StepIdx

namespace GlobalTheory.CompanionTheory.IwJac

end GlobalTheory.CompanionTheory.IwJac

end
