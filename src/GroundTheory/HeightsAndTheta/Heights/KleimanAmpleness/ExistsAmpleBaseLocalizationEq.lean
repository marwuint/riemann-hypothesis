import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosedLocal
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section LocRings

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem coe_ne_zero_of_not_mem_ideal {A : Subalgebra S Ω} {p : Ideal A} {b : A} (hb : b ∉ p) : (b : Ω) ≠ 0 := by
  intro h
  apply hb
  rw [show b = 0 from Subtype.ext h]
  exact p.zero_mem

theorem mem_locIn_iff (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] (z : Ω) :
    z ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p ↔ ∃ a b : A, b ∉ p ∧ z = a / b := by
  have h1 : (1 : A) ∉ p := fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  constructor
  · intro hz
    let R : Subring Ω :=
      { carrier := {z | ∃ a b : A, b ∉ p ∧ z = a / b}
        mul_mem' := by
          rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
          exact ⟨a * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', by
            simp only [Subalgebra.coe_mul]; rw [div_mul_div_comm]⟩
        one_mem' := ⟨1, 1, h1, by simp⟩
        add_mem' := by
          rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
          exact ⟨a * b' + b * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', by
            simp only [Subalgebra.coe_mul, Subalgebra.coe_add]
            rw [div_add_div _ _ (coe_ne_zero_of_not_mem_ideal hb) (coe_ne_zero_of_not_mem_ideal hb')]⟩
        zero_mem' := ⟨0, 1, h1, by simp⟩
        neg_mem' := by
          rintro _ ⟨a, b, hb, rfl⟩
          exact ⟨-a, b, hb, by simp [neg_div]⟩ }
    have hle : IndefiniteRowSideFullHecke.Kleiman2.locIn A p ≤ R := Subring.closure_le.mpr fun z hz => hz
    exact hle hz
  · rintro ⟨a, b, hb, rfl⟩
    exact Subring.subset_closure ⟨a, b, hb, rfl⟩

theorem le_locInV (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  (mem_locIn_iff A p a).mpr ⟨⟨a, ha⟩, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩

def locAlg (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] : Subalgebra S Ω :=
  { (IndefiniteRowSideFullHecke.Kleiman2.locIn A p).toSubsemiring with
    algebraMap_mem' := fun r => le_locInV A p (A.algebraMap_mem r) }

theorem mem_locAlg {A : Subalgebra S Ω} {p : Ideal A} [p.IsPrime] {z : Ω} :
    z ∈ locAlg A p ↔ z ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p := Iff.rfl

def locMax (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] : Ideal (locAlg A p) where
  carrier := {z | ∃ a b : A, a ∈ p ∧ b ∉ p ∧ (z : Ω) = a / b}
  add_mem' := by
    rintro z z' ⟨a, b, ha, hb, hz⟩ ⟨a', b', ha', hb', hz'⟩
    refine ⟨a * b' + b * a', b * b', p.add_mem (p.mul_mem_right _ ha) (p.mul_mem_left _ ha'),
      fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
    rw [hz, hz', div_add_div _ _ (coe_ne_zero_of_not_mem_ideal hb) (coe_ne_zero_of_not_mem_ideal hb')]
  zero_mem' := ⟨0, 1, p.zero_mem, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  smul_mem' := by
    rintro c z ⟨a, b, ha, hb, hz⟩
    obtain ⟨u, v, hv, hc⟩ := (mem_locIn_iff A p c).mp c.2
    refine ⟨u * a, v * b, p.mul_mem_left _ ha, fun h => (hp.mem_or_mem h).elim hv hb, ?_⟩
    simp only [smul_eq_mul, Subalgebra.coe_mul]
    rw [hz, hc, div_mul_div_comm]

theorem locMax_isPrime (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] : (locMax A p).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ne, Ideal.eq_top_iff_one]
    rintro ⟨a, b, ha, hb, h1⟩
    have hb0 := coe_ne_zero_of_not_mem_ideal hb
    have hab : (a : Ω) = b := by
      rw [eq_div_iff hb0] at h1
      simpa using h1.symm
    exact hb (by rw [show b = a from Subtype.ext hab.symm]; exact ha)
  · rintro z z' ⟨a, b, ha, hb, hzz⟩
    obtain ⟨u, v, hv, hz⟩ := (mem_locIn_iff A p z).mp z.2
    obtain ⟨u', v', hv', hz'⟩ := (mem_locIn_iff A p z').mp z'.2
    have hv0 := coe_ne_zero_of_not_mem_ideal hv
    have hv0' := coe_ne_zero_of_not_mem_ideal hv'
    have hb0 := coe_ne_zero_of_not_mem_ideal hb
    have key : u * u' * b = a * (v * v') := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul] at hzz ⊢
      rw [hz, hz', div_mul_div_comm, div_eq_div_iff (mul_ne_zero hv0 hv0') hb0] at hzz
      rw [hzz]
    have hmem : u * u' * b ∈ p := by rw [key]; exact p.mul_mem_right _ ha
    rcases hp.mem_or_mem hmem with h | h
    · rcases hp.mem_or_mem h with h | h
      · exact Or.inl ⟨u, v, h, hv, hz⟩
      · exact Or.inr ⟨u', v', h, hv', hz'⟩
    · exact absurd h hb

instance (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] : (locMax A p).IsPrime := locMax_isPrime A p

end LocRings

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
