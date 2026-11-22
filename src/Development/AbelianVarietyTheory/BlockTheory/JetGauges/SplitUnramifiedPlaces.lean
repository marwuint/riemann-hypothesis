import Mathlib

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

section Ring

variable (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]

abbrev Op : Type := ℤ_[p] ⊗[ℤ] OE

def bar [StarRing OE] : Op p OE ≃ₐ[ℤ_[p]] Op p OE :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p])
    (AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut OE)) (fun n => by simp))

variable {p OE}

@[simp] theorem bar_tmul [StarRing OE] (z : ℤ_[p]) (a : OE) :
    bar p OE (z ⊗ₜ a) = z ⊗ₜ star a := rfl

theorem bar_bar [StarRing OE] (x : Op p OE) : bar p OE (bar p OE x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z a => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def extend {O : Type} [CommRing O] [Algebra ℤ_[p] O] (σ : OE →+* O) : Op p OE →ₐ[ℤ_[p]] O :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] O) σ.toIntAlgHom (fun _ _ => Commute.all _ _)

@[simp] theorem extend_tmul {O : Type} [CommRing O] [Algebra ℤ_[p] O] (σ : OE →+* O)
    (z : ℤ_[p]) (a : OE) : extend σ (z ⊗ₜ a : Op p OE) = algebraMap ℤ_[p] O z * σ a := rfl

end Ring

@[ext] structure Place (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] where

  e : Op p OE
  idem : IsIdempotentElem e
  ne_zero : e ≠ 0
  primitive : ∀ f : Op p OE, IsIdempotentElem f → f * e = f → f = 0 ∨ f = e

namespace Place

variable {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE]

def conj [StarRing OE] (w : Place p OE) : Place p OE where
  e := bar p OE w.e
  idem := w.idem.map (bar p OE)
  ne_zero := fun h => w.ne_zero (by rw [← bar_bar w.e, h, map_zero])
  primitive := fun f hf h => by
    rcases w.primitive (bar p OE f) (hf.map (bar p OE))
      (by rw [← bar_bar w.e, ← map_mul, h]) with h0 | h1
    · left; rw [← bar_bar f, h0, map_zero]
    · right; rw [← h1, bar_bar]

theorem conj_conj [StarRing OE] (w : Place p OE) : w.conj.conj = w :=
  Place.ext (bar_bar w.e)

abbrev Ow (w : Place p OE) : Type := Op p OE ⧸ Ideal.span {1 - w.e}

def toOw (w : Place p OE) : OE →+* w.Ow :=
  (Ideal.Quotient.mk _).comp
    (Algebra.TensorProduct.includeRight : OE →ₐ[ℤ] Op p OE).toRingHom

def degree [Module.Finite ℤ OE] (w : Place p OE) : ℕ := Module.finrank ℤ_[p] w.Ow

end Place

structure SplitPlace (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [StarRing OE]
    extends Place p OE where
  ne_conj : toPlace ≠ toPlace.conj

def SplitPlace.conj {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] [StarRing OE]
    (w : SplitPlace p OE) : SplitPlace p OE where
  toPlace := w.toPlace.conj
  ne_conj := by rw [Place.conj_conj]; exact w.ne_conj.symm

section Gauss

variable {p : ℕ} [Fact p.Prime]

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

end Gauss

end GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
