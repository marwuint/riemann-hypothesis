import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ThetaWeightHeightConstants

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField Matrix
open scoped ComplexOrder

variable {R : Ranks}

abbrev Pl (R : Ranks) : Type := ↥(R.Psi)

instance instFintypePl : Fintype (Pl R) := Fintype.ofFinite _

def tau (H : Host R) (τ : Pl R) : H.E →+* ℂ := H.emb τ.1

theorem conj_conj (H : Host R) (x : H.E) : H.conj (H.conj x) = x :=
  H.φ₀.injective (by
    rw [show H.φ₀ (H.conj (H.conj x)) = _ from H.conjE_apply _ _,
      show H.φ₀ (H.conj x) = _ from H.conjE_apply _ _]
    simp)

abbrev V (H : Host R) (n : ℕ) : Type := Fin n → H.E

variable {H : Host R} {n : ℕ}

def idealMul (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) (N : Submodule (𝓞 H.E) (V H n)) :
    Submodule (𝓞 H.E) (V H n) :=
  Submodule.span (𝓞 H.E) {w | ∃ a ∈ 𝔞, ∃ v ∈ N, w = a • v}

theorem smul_dot (a : 𝓞 H.E) (y x : V H n) : (a • y) ⬝ᵥ x = y ⬝ᵥ (a • x) := by
  rw [smul_dotProduct, dotProduct_smul]

def dualZ (X : Submodule (𝓞 H.E) (V H n)) : Submodule (𝓞 H.E) (V H n) where
  carrier := {y | ∀ x ∈ X, ∃ z : ℤ, Algebra.trace ℚ H.E (y ⬝ᵥ x) = z}
  add_mem' := fun {y y'} hy hy' x hx => by
    obtain ⟨z, h⟩ := hy x hx
    obtain ⟨z', h'⟩ := hy' x hx
    exact ⟨z + z', by rw [add_dotProduct, map_add, h, h']; push_cast; rfl⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := fun a y hy x hx => by rw [smul_dot]; exact hy _ (X.smul_mem a hx)

def cochar (N : Submodule (𝓞 H.E) (V H n)) : Submodule (𝓞 H.E) (V H n) := idealMul H.AA N

def charLattice (N : Submodule (𝓞 H.E) (V H n)) : Submodule (𝓞 H.E) (V H n) := dualZ (cochar N)

def Herm (H : Host R) (n : ℕ) : Submodule ℚ (Matrix (Fin n) (Fin n) H.E) where
  carrier := {χ | ∀ i k, χ k i = H.conj (χ i k)}
  add_mem' := fun {a b} ha hb i k => by simp [ha i k, hb i k]
  zero_mem' := fun i k => by simp
  smul_mem' := fun q a ha i k => by
    simp only [Matrix.smul_apply, ha i k, Rat.smul_def, map_mul, map_ratCast]

def val (χ : Herm H n) (y y' : V H n) : H.E :=
  ∑ i, ∑ k, y i * (χ : Matrix (Fin n) (Fin n) H.E) i k * H.conj (y' k)

def symForm (x x' : V H n) : Herm H n :=
  ⟨Matrix.of fun i k => x i * H.conj (x' k) + x' i * H.conj (x k), fun i k => by
    simp only [Matrix.of_apply, map_add, map_mul, conj_conj]; ring⟩

def levelOne (X : Submodule (𝓞 H.E) (V H n)) : AddSubgroup (Herm H n) :=
  AddSubgroup.closure {χ | ∃ x ∈ X, ∃ x' ∈ X, χ = symForm x x'}

def level (H : Host R) : ℕ := H.g 0 * H.g 1

def expGroup (X : Submodule (𝓞 H.E) (V H n)) : AddSubgroup (Herm H n) :=
  (levelOne X).comap (nsmulAddMonoidHom (level H))

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants

end GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents

end
