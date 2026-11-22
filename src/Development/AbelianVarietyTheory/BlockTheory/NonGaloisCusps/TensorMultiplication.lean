import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorMultiplication

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Maps

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem actVB_mulVB (ρ : Representation LL G V) (g : G) (c : K₀) (x : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (LL := LL) c x) = mulVB (K₀ := K₀) (LL := LL) c (actVB PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, mulVB]
  | add a b ha hb => simp only [map_add, ha, hb]

omit [IsScalarTower Qp K₀ B] in

theorem comm_smul [SMulCommClass Qp K₀ B] (c : K₀) (x : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (c • x) =
      mulVB (K₀ := K₀) (LL := LL) c (TensorProduct.comm Qp B V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => simp [mulVB, TensorProduct.smul_tmul', Algebra.smul_def]
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]

def DcrisK (ρ : Representation LL G V) : Submodule K₀ (B ⊗[Qp] V) where
  carrier := {x | TensorProduct.comm Qp B V x ∈ Dcris PD ρ}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact (Dcris PD ρ).add_mem ha hb
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    rw [comm_smul (LL := LL), actVB_mulVB, hx g]

def compMap (ρ : Representation LL G V) : B ⊗[K₀] ↥(DcrisK PD ρ) →ₗ[B] B ⊗[Qp] V :=
  LinearMap.liftBaseChange B (DcrisK PD ρ).subtype

def Equivariant (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V') : Prop :=
  ∀ g x, f (ρ g x) = ρ' g (f x)

variable (Qp B LL V V') in

def mulTens : (V ⊗[Qp] B) ⊗[LL] (V' ⊗[Qp] B) →ₗ[LL] (V ⊗[LL] V') ⊗[Qp] B :=
  (AlgebraTensorModule.map (LinearMap.id : V ⊗[LL] V' →ₗ[LL] V ⊗[LL] V') (LinearMap.mul' Qp B)).comp
    (AlgebraTensorModule.tensorTensorTensorComm Qp Qp LL LL V B V' B).toLinearMap

end Maps

def InvB : Prop := ∀ b : B, (∀ g, PD.actB g b = b) ↔ ∃ c : K₀, algebraMap K₀ B c = b

variable (LL : Type) [Field LL] [Algebra Qp LL]

def Comparison : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    IsCrys PD ρ → Function.Bijective (compMap PD ρ)

def CrysSub : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V') (f : V' →ₗ[LL] V),
    Equivariant ρ' ρ f → Function.Injective f → IsCrys PD ρ → IsCrys PD ρ'

def CrysQuot : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V') (f : V →ₗ[LL] V'),
    Equivariant ρ ρ' f → Function.Surjective f → IsCrys PD ρ → IsCrys PD ρ'

def CrysSum : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' → IsCrys PD (ρ.prod ρ')

def CrysTensor : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' → IsCrys PD (ρ.tprod ρ')

def CrysDual : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    IsCrys PD ρ → IsCrys PD ρ.dual

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.TensorMultiplication
