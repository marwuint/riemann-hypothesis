import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.IsHaarMeasureDoubledGroup
import Mathlib
import GroundTheory.GlobalFields.Adele.Compact

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.EisBL.DoubledUnipotentRadical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem matrixRep_mul {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (a b : G2 σ Y) : mat2 (a * b) = mat2 a * mat2 b := rfl

omit [NumberField E] in
theorem matrixRep_one {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} : mat2 (1 : G2 σ Y) = 1 := rfl

omit [NumberField E] in
theorem cA_inclR (σ : E →ₐ[F] E) (x : E) :
    cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

omit [NumberField E] in
theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ
      (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end GlobalTheory.EisBL.DoubledUnipotentRadical
