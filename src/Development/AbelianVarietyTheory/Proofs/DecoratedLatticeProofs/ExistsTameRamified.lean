import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamLine

variable {D : D7}

def intRing (D : D7) : Subring (AE D) := (GlobalTheory.CharFin.hatRing D.host.F D.host.E).comap (finPart D)

theorem mem_intRing (z : AE D) : z ∈ intRing D ↔ finPart D z ∈ intAE D := by
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact Iff.rfl

theorem finPart_cA (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem cA_mem {z : AE D} (hz : z ∈ intRing D) : cA D z ∈ intRing D := by
  rw [mem_intRing] at hz ⊢
  rw [finPart_cA]
  have : intAE D ≤ (intAE D).comap (sigR (Af D.host.F) D.sp.cm.sig).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, rfl⟩
    exact AddSubgroup.subset_closure
      ⟨a, ha, RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E) x, rfl⟩
  exact this hz

def Dvd (N : ℕ) (z : AE D) : Prop :=
  ∃ w ∈ GlobalTheory.CharFin.hatRing D.host.F D.host.E, finPart D z = (N : Af D.host.F ⊗[D.host.F] D.host.E) * w

theorem Dvd.add {N : ℕ} {y z : AE D} (hy : Dvd N y) (hz : Dvd N z) : Dvd N (y + z) := by
  obtain ⟨a, ha, e⟩ := hy
  obtain ⟨b, hb, e'⟩ := hz
  exact ⟨a + b, add_mem ha hb, by rw [RingHom.map_add, e, e', mul_add]⟩

theorem Dvd.mul {N : ℕ} {y z : AE D} (hy : Dvd N y) (hz : z ∈ intRing D) : Dvd N (y * z) := by
  obtain ⟨a, ha, e⟩ := hy
  exact ⟨a * finPart D z, mul_mem ha hz, by rw [map_mul, e, mul_assoc]⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (p : SplitPt D k)

def Near (N : ℕ) (y : AE D) : Prop :=
  cA D y * y = 1 ∧ y ∈ intRing D ∧ Dvd N ((1 - (p.e + cA D p.e)) * (y - 1)) ∧ valuation k (p.pr y - 1) < 1

variable {p} {N : ℕ}

theorem Near.val {y : AE D} (h : Near p N y) : valuation k (p.pr y) = 1 := by
  have := Valuation.map_one_add_of_lt (valuation k) h.2.2.2
  rwa [add_sub_cancel] at this

theorem Near.mul {y z : AE D} (hy : Near p N y) (hz : Near p N z) : Near p N (y * z) := by
  refine ⟨?_, mul_mem hy.2.1 hz.2.1, ?_, ?_⟩
  · rw [map_mul, mul_mul_mul_comm, hy.1, hz.1, mul_one]
  · convert (hy.2.2.1.mul hz.2.1).add hz.2.2.1 using 1
    ring
  · have : p.pr (y * z) - 1 = (p.pr y - 1) * p.pr z + (p.pr z - 1) := by rw [map_mul]; ring
    rw [this]
    refine Valuation.map_add_lt _ ?_ hz.2.2.2
    rw [map_mul, hz.val, mul_one]
    exact hy.2.2.2

theorem Near.conj {y : AE D} (hy : Near p N y) : Near p N (cA D y) := by
  refine ⟨by rw [cA_cA', mul_comm, hy.1], cA_mem hy.2.1, ?_, ?_⟩
  · convert hy.2.2.1.mul (neg_mem (cA_mem hy.2.1)) using 1
    linear_combination (1 - (p.e + cA D p.e)) * hy.1
  · have h1 : p.pr (cA D y) * p.pr y = 1 := by rw [← map_mul, hy.1, map_one]
    have h2 : valuation k (p.pr (cA D y)) = 1 := by
      have := congrArg (valuation k) h1
      rwa [map_mul, hy.val, mul_one, map_one] at this
    have : p.pr (cA D y) - 1 = -((p.pr y - 1) * p.pr (cA D y)) := by linear_combination h1
    rw [this, Valuation.map_neg, map_mul, h2, mul_one]
    exact hy.2.2.2

end GlobalTheory.RamLine
