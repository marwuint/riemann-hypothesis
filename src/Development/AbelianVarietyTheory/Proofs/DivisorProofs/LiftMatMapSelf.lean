import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.CompIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mapNU_mul {A B : Type} [CommRing A] [CommRing B] {m : ℕ} (S : A →ₙ+* B) (X Y : Matrix (Fin m) (Fin m) A) :
    (X * Y).map S = X.map S * Y.map S := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

def liftMat (v : Pl F) (m : ℕ) : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E) →* Matrix (Fin m) (Fin m) (AE F E) where
  toFun h := 1 + (h - 1).map (Supp.singleTens E v)
  map_one' := by simp
  map_mul' a b := by
    have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    rw [e, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), mapNU_mul]
    noncomm_ring

theorem liftMat_apply (v : Pl F) {m : ℕ} (h : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) :
    liftMat v m h = 1 + (h - 1).map (Supp.singleTens E v) := rfl

variable (σ : E →ₐ[F] E) {m : ℕ} (Y : Spc F E m) (v : Pl F)

end GlobalTheory.HoweLocal.CompIso

namespace GlobalTheory.HoweLocal

end GlobalTheory.HoweLocal
