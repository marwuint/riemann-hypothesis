import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped TensorProduct

namespace GlobalTheory.ResW

def blkE {r s N : ℕ} (h : r + s = N) : Fin r ⊕ Fin s ≃ Fin N := finSumFinEquiv.trans (finCongr h)

def blkM (R : Type) [CommRing R] {r s N : ℕ} (h : r + s = N) :
    Matrix (Fin r) (Fin r) R × Matrix (Fin s) (Fin s) R →* Matrix (Fin N) (Fin N) R where
  toFun p := Matrix.reindex (blkE h) (blkE h) (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def blk {R : Type} [CommRing R] {r s N : ℕ} (h : r + s = N) : GL (Fin r) R × GL (Fin s) R →* GL (Fin N) R :=
  (Units.map (blkM R h)).comp MulEquiv.prodUnits.symm.toMonoidHom

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N r s m a : ℕ}

variable (E) in

def nu (t : ℝ) : HChar E := GlobalTheory.HeckeGal.Model.absPow E t

variable (E) in

abbrev Letter : Type := Σ a : ℕ, CuspSub E a

def wsize (u : List (Letter E)) : ℕ := (u.map (·.1)).sum

noncomputable def Vec : List (Letter E) → Type
  | [] => PUnit
  | x :: u => x.2.V × Vec u

variable (E N) in

def zc : Module.End ℂ (Sm E N) := lie E N fun i j => if i = j then 1 else 0

def cex (x : Letter E) : ℂ := Classical.epsilon fun c : ℂ => ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ

def rexp (x : Letter E) : ℝ := (cex x).re / (x.1 * Module.finrank ℚ E)

def tw (x : Letter E) (t : ℝ) : Letter E := ⟨x.1, x.2.twist (nu E t)⟩

def SatVec (φ : Sm E N) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop :=
  ∀ᶠ v in Filter.cofinite, GlobalTheory.LFun.IsSatVecGL v ((finRep E N).comp (locGL E N v)) φ (B v)

def SatFam (V : Submodule ℂ (Sm E N)) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop := ∀ φ ∈ V, φ ≠ 0 → SatVec φ B

end GlobalTheory.ResW

end
