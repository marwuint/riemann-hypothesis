import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem singleFin_mul (v : Pl F) (a b : Fv F v) :
    GlobalTheory.AdelicU.singleFin v (a * b) = GlobalTheory.AdelicU.singleFin v a * GlobalTheory.AdelicU.singleFin v b := by
  apply GlobalTheory.AdelicU.af_ext
  intro u
  rw [map_mul (evalV F u)]
  by_cases hu : u = v
  · subst hu
    rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, zero_mul]

theorem liftV_mul (v : Pl F) (a b : Fv F v) :
    GlobalTheory.LatVac.liftV v (a * b) = GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b := by
  change ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v (a * b)) =
    ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a) * ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v b)
  rw [Prod.mk_mul_mk, mul_zero, singleFin_mul]

theorem liftE_mul (v : Pl F) (x y : Fv F v ⊗[F] E) : liftE v (x * y) = liftE v x * liftE v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | tmul b f =>
      simp only [liftE, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
        liftV_mul]

theorem one_add_liftE_mul (v : Pl F) (x y : Fv F v ⊗[F] E) :
    (1 + liftE v (x - 1)) * (1 + liftE v (y - 1)) = 1 + liftE v (x * y - 1) := by
  have : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by ring
  rw [this, map_add, map_add, liftE_mul]
  ring

theorem one_add_liftV_mul (v : Pl F) (x y : Fv F v) :
    (1 + GlobalTheory.LatVac.liftV v (x - 1)) * (1 + GlobalTheory.LatVac.liftV v (y - 1)) = 1 + GlobalTheory.LatVac.liftV v (x * y - 1) := by
  have : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by ring
  rw [this, map_add, map_add, liftV_mul]
  ring

def liftU (v : Pl F) : (Fv F v ⊗[F] E)ˣ →* (AE F E)ˣ where
  toFun z := ⟨1 + liftE v ((z : Fv F v ⊗[F] E) - 1), 1 + liftE v (((z⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) - 1),
    by rw [one_add_liftE_mul, Units.mul_inv, sub_self, map_zero, add_zero],
    by rw [one_add_liftE_mul, Units.inv_mul, sub_self, map_zero, add_zero]⟩
  map_one' := by ext; simp
  map_mul' z w := by ext; simp only [Units.val_mul, Units.val_mk]; rw [one_add_liftE_mul]

def liftUF (v : Pl F) : (Fv F v)ˣ →* (AF F)ˣ where
  toFun a := ⟨1 + GlobalTheory.LatVac.liftV v ((a : Fv F v) - 1), 1 + GlobalTheory.LatVac.liftV v (((a⁻¹ : (Fv F v)ˣ) : Fv F v) - 1),
    by rw [one_add_liftV_mul, Units.mul_inv, sub_self, map_zero, add_zero],
    by rw [one_add_liftV_mul, Units.inv_mul, sub_self, map_zero, add_zero]⟩
  map_one' := by ext; simp
  map_mul' z w := by ext; simp only [Units.val_mul, Units.val_mk]; rw [one_add_liftV_mul]

theorem liftU_val (v : Pl F) (z : (Fv F v ⊗[F] E)ˣ) :
    ((liftU v z : (AE F E)ˣ) : AE F E) = 1 + liftE v ((z : Fv F v ⊗[F] E) - 1) := rfl

theorem liftUF_val (v : Pl F) (a : (Fv F v)ˣ) :
    ((liftUF v a : (AF F)ˣ) : AF F) = 1 + GlobalTheory.LatVac.liftV v ((a : Fv F v) - 1) := rfl

end GlobalTheory.HoweLocal

namespace GlobalTheory.HoweLocal

end GlobalTheory.HoweLocal

namespace GlobalTheory.HoweLocal

end GlobalTheory.HoweLocal

namespace GlobalTheory.HoweLocal

end GlobalTheory.HoweLocal
