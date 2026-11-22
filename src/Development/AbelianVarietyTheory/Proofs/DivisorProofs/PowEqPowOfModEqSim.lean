import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyIso

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime]

structure SimSys (D : Datum p) (N K : ℕ) where
  g : ℕ → D.La →+ D.La
  u : ℕ → ℕ
  lin : ∀ n, 0 < n → n.Coprime p → ∀ (c : D.O) x, ∃ z, g n (c • x) = c • g n x + n • z
  u_cop : ∀ n, 0 < n → n.Coprime p → (u n).Coprime n
  u_tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → u (n * m) ≡ u n [MOD n]
  surj : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z
  inj : ∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w
  sim : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y, (n : ℤ) ∣ D.EF (g n x) (g n y) - u n * D.EF x y
  tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z
  one : ∀ x, ∃ z, g K x = x + N • z

variable {D : Datum p} {N K : ℕ}

def SimSys.id : SimSys D N K where
  g _ := AddMonoidHom.id _
  u _ := 1
  lin _ _ _ c x := ⟨0, by simp⟩
  u_cop _ _ _ := Nat.coprime_one_left _
  u_tower _ _ _ _ _ := rfl
  surj _ _ _ x := ⟨x, 0, by simp⟩
  inj _ _ _ x z h := ⟨z, h⟩
  sim _ _ _ x y := by simp
  tower _ _ _ _ _ x := ⟨0, by simp⟩
  one x := ⟨0, by simp⟩

def SimSys.comp (s t : SimSys D N K) : SimSys D N K where
  g n := (s.g n).comp (t.g n)
  u n := s.u n * t.u n
  lin n hn hc c x := by
    obtain ⟨z, hz⟩ := t.lin n hn hc c x
    obtain ⟨z', hz'⟩ := s.lin n hn hc c (t.g n x)
    exact ⟨z' + s.g n z, by simp only [AddMonoidHom.comp_apply]; rw [hz, map_add, hz', map_nsmul, smul_add, add_assoc]⟩
  u_cop n hn hc := Nat.Coprime.mul (s.u_cop n hn hc) (t.u_cop n hn hc)
  u_tower n m hn hm hc := Nat.ModEq.mul (s.u_tower n m hn hm hc) (t.u_tower n m hn hm hc)
  surj n hn hc x := by
    obtain ⟨y, z, hy⟩ := s.surj n hn hc x
    obtain ⟨y', z', hy'⟩ := t.surj n hn hc y
    exact ⟨y', z + s.g n z', by simp only [AddMonoidHom.comp_apply]; rw [hy', map_add, hy, map_nsmul, smul_add, add_assoc]⟩
  inj n hn hc x z h := by
    obtain ⟨w, hw⟩ := s.inj n hn hc (t.g n x) z h
    exact t.inj n hn hc x w hw
  sim n hn hc x y := by
    have h₁ := s.sim n hn hc (t.g n x) (t.g n y)
    have h₂ := t.sim n hn hc x y
    have e : D.EF ((s.g n).comp (t.g n) x) ((s.g n).comp (t.g n) y) - ((s.u n * t.u n : ℕ) : ℤ) * D.EF x y =
        (D.EF (s.g n (t.g n x)) (s.g n (t.g n y)) - s.u n * D.EF (t.g n x) (t.g n y)) +
        s.u n * (D.EF (t.g n x) (t.g n y) - t.u n * D.EF x y) := by
      simp only [AddMonoidHom.comp_apply]; push_cast; ring
    rw [e]
    exact dvd_add h₁ (dvd_mul_of_dvd_right h₂ _)
  tower n m hn hm hc x := by
    obtain ⟨z, hz⟩ := t.tower n m hn hm hc x
    obtain ⟨z', hz'⟩ := s.tower n m hn hm hc (t.g n x)
    exact ⟨z' + s.g (n * m) z, by
      simp only [AddMonoidHom.comp_apply]
      rw [hz, map_add, hz', map_nsmul, smul_add, add_assoc]⟩
  one x := by
    obtain ⟨z, hz⟩ := t.one x
    obtain ⟨z', hz'⟩ := s.one x
    exact ⟨z' + s.g K z, by
      simp only [AddMonoidHom.comp_apply]
      rw [hz, map_add, hz', map_nsmul, smul_add, add_assoc]⟩

section Tate

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem TateIsoO.ev_nsmul_self (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) (z : D.La) :
    I.ev n (n • z) = 1 :=
  (I.ker n hn hc _).2 ⟨z, rfl⟩

theorem TateIsoO.ev_add_nsmul (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) (x z : D.La) :
    I.ev n (x + n • z) = I.ev n x := by
  rw [I.add, I.ev_nsmul_self hn hc, _root_.mul_one]

end Tate

variable {R : Type} [CommRing R]

variable (D K) in

def multSub : AddSubgroup D.La where
  carrier := {x | ∃ z, x = K • z}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨c, rfl⟩
    exact ⟨a + c, (smul_add _ _ _).symm⟩
  zero_mem' := ⟨0, (smul_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, (smul_neg _ _).symm⟩

variable (D K) in

abbrev LQ := D.La ⧸ multSub D K

def SimSys.Lifts (t : SimSys D N K) (a : Equiv.Perm (LQ D K)) : Prop :=
  ∀ y, a (QuotientAddGroup.mk y) = QuotientAddGroup.mk (t.g K y)

theorem SimSys.lifts_one : (SimSys.id : SimSys D N K).Lifts 1 := fun _ => rfl

theorem SimSys.Lifts.comp {s t : SimSys D N K} {a c : Equiv.Perm (LQ D K)} (hs : s.Lifts a) (ht : t.Lifts c) :
    (s.comp t).Lifts (a * c) := fun y => by rw [Equiv.Perm.mul_apply, ht, hs]; rfl

variable (D N K) in

def levelGrp : Subgroup (Equiv.Perm (LQ D K)) where
  carrier := {a | (∃ t : SimSys D N K, t.Lifts a) ∧ ∃ t : SimSys D N K, t.Lifts a⁻¹}
  one_mem' := ⟨⟨SimSys.id, SimSys.lifts_one⟩, ⟨SimSys.id, by rw [inv_one]; exact SimSys.lifts_one⟩⟩
  mul_mem' := by
    rintro a c ⟨⟨s, hs⟩, ⟨s', hs'⟩⟩ ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩
    exact ⟨⟨s.comp t, hs.comp ht⟩, ⟨t'.comp s', by rw [mul_inv_rev]; exact ht'.comp hs'⟩⟩
  inv_mem' := by
    rintro a ⟨h₁, h₂⟩
    exact ⟨h₂, by rw [inv_inv]; exact h₁⟩

end GlobalTheory.UPel.HT
