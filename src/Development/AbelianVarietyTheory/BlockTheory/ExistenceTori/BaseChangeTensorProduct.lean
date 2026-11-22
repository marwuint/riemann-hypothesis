import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveComp
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps

set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeTensorProduct

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped TensorProduct

section BaseChange

variable {K L : Type} [Field K] [Field L] [Algebra K L] {σ : K →+* ℂ} {σ' : L →+* ℂ}
  {C W : Type} [AddCommGroup C] [Module K C] [AddCommGroup W] [Module ℂ W]

def bcBil (σ' : L →+* ℂ) (f : C →ₛₗ[σ] W) : L →+ C →+ W where
  toFun t := (DistribSMul.toAddMonoidHom W (σ' t)).comp f.toAddMonoidHom
  map_zero' := by ext F : 1; simp
  map_add' s t := by ext F : 1; simp [add_smul]

theorem bcBil_apply (σ' : L →+* ℂ) (f : C →ₛₗ[σ] W) (t : L) (x : C) : bcBil σ' f t x = σ' t • f x := rfl

def bcAdd (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) : L ⊗[K] C →+ W :=
  TensorProduct.liftAddHom (bcBil σ' f) fun a t x => by
    rw [bcBil_apply, bcBil_apply, LinearMap.map_smulₛₗ, Algebra.smul_def a t, map_mul, hσ a, smul_smul, mul_comm]

theorem bcAdd_tmul (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) (t : L) (x : C) :
    bcAdd hσ f (t ⊗ₜ x) = σ' t • f x := rfl

def bcMap (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) : L ⊗[K] C →ₛₗ[σ'] W where
  toFun := bcAdd hσ f
  map_add' := map_add _
  map_smul' s x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t F => rw [TensorProduct.smul_tmul', bcAdd_tmul, bcAdd_tmul, smul_eq_mul, map_mul, mul_smul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

end BaseChange

variable {D : D7}

section Forms

variable (T : Core D) (j : ℕ)

abbrev Cf (w : WeightFamilies.Wt D j) : Type := cutR T.C j w

instance instAddCommGroupCf (w : WeightFamilies.Wt D j) : AddCommGroup (Cf T j w) := Submodule.addCommGroup _

instance instModuleCf (w : WeightFamilies.Wt D j) : Module T.Q.c.F (Cf T j w) := Submodule.module _

def rd (w : WeightFamilies.Wt D j) : Cf T j w →ₛₗ[T.σ₀] FDSec (T.X₀ j) :=
  (rdU (T.U j T.σ₀)).comp (cutR T.C j w).subtype

end Forms

section Generic

variable (T : Core D) (j N : ℕ)

abbrev KT : Type := FractionRing (MvPolynomial (Gaps.EtaleWeightGaps.Idx D j N) T.Q.c.F)

variable {T j N}

def IsExt (σ' : KT T j N →+* ℂ) : Prop := ∀ a : T.Q.c.F, σ' (algebraMap T.Q.c.F (KT T j N) a) = T.σ₀ a

variable (T j N) in

abbrev CfT (w : WeightFamilies.Wt D j) : Type := KT T j N ⊗[T.Q.c.F] Cf T j w

instance instModuleCfT (w : WeightFamilies.Wt D j) : Module (KT T j N) (CfT T j N w) := TensorProduct.leftModule

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeTensorProduct
