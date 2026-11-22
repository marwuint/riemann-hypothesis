import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
import Formalism.PeriodIntegrals.CuspInfChar

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.GLTwoHecke

section Matrices

variable {R : Type} [CommRing R]

def dg (a b : Rˣ) : GL (Fin 2) R :=
  ⟨!![(a : R), 0; 0, (b : R)], !![((a⁻¹ : Rˣ) : R), 0; 0, ((b⁻¹ : Rˣ) : R)],
    by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

def up (b : R) : GL (Fin 2) R :=
  ⟨!![1, b; 0, 1], !![1, -b; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

variable (R) in

def wy : GL (Fin 2) R :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

@[simp] theorem dg_val (a b : Rˣ) : (dg a b).1 = !![(a : R), 0; 0, (b : R)] := rfl
@[simp] theorem up_val (b : R) : (up b).1 = !![1, b; 0, 1] := rfl
@[simp] theorem wy_val : (wy R).1 = !![0, 1; 1, 0] := rfl

end Matrices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def singleNU (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →ₙ+* FiniteAdeleRing (𝓞 E) E where
  toFun := singleFin w
  map_mul' := singleFin_mul w
  map_zero' := map_zero _
  map_add' := map_add _

end GlobalTheory.GLTwoHecke

end
