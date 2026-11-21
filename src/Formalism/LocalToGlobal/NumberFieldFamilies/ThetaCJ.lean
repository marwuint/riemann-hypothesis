import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCN

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

theorem alg_trace_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (h : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, add_add_add_comm]
  | tmul a e =>
    have h4 : (a ⊗ₜ[F] e : R ⊗[F] E) = a • inclR R e := by
      show _ = a • ((1 : R) ⊗ₜ[F] e)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h5 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h5, ← TensorProduct.tmul_add, ← h, h4, map_smul, trace_gen, smul_eq_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one (A := E), ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_comm]

end Gen

variable {D : D7}

variable {V W : HSp D}

theorem actHom_add (g : GA D V) (h : GA D W) (x y : WA V W) :
    actHom V W g h (x + y) = actHom V W g h x + actHom V W g h y := by
  unfold actHom
  split_ifs <;> rw [Matrix.mul_add, Matrix.add_mul]

variable (D) in

def iE : AE D := mkAE (fun _ => Complex.I) 0

def fockJ (s : GA D V) (t : GA D W) : WA V W →+ WA V W :=
  AddMonoidHom.mk' (fun x => iE D • actHom V W s t x) fun x y => by rw [actHom_add, smul_add]

theorem fockJ_apply (s : GA D V) (t : GA D W) (x : WA V W) : fockJ s t x = iE D • actHom V W s t x := rfl

end Formalism.L2.Fam.ThC

end
