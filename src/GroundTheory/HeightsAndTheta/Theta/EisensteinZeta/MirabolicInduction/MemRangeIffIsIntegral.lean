import Mathlib
import GroundTheory.AutomorphicForms.HermitianSpaces
import GroundTheory.HeightsAndTheta.Heights.HermitianLattice
import GroundTheory.AutomorphicForms.HermitianDisc
import GroundTheory.HeightsAndTheta.Theta.CMDatum
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.DedekindZetaSeries.ChainWittIndexHypothesesMet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

namespace FunctionalEquationAlt

open NumberField TensorProduct Module GroundTheory.Automorphic
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

def CAt {E : Type} [Field E] (_σ : E →+* ℂ) : Type := ℂ

namespace CAt

variable {E : Type} [Field E] (σ : E →+* ℂ)

instance : Field (CAt σ) := inferInstanceAs (Field ℂ)

instance : Algebra ℂ (CAt σ) := inferInstanceAs (Algebra ℂ ℂ)

def ofComplex : ℂ ≃ₐ[ℂ] CAt σ := AlgEquiv.refl

instance : Algebra E (CAt σ) := ((ofComplex σ).toRingHom.comp σ).toAlgebra

theorem algebraMap_apply (a : E) : algebraMap E (CAt σ) a = ofComplex σ (σ a) := rfl

theorem smul_def (a : E) (z : CAt σ) : a • z = ofComplex σ (σ a) * z := rfl

theorem complex_smul_def (c : ℂ) (z : CAt σ) : c • z = ofComplex σ c * z := rfl

instance : SMulCommClass E ℂ (CAt σ) where
  smul_comm a c z := by
    rw [smul_def, complex_smul_def, complex_smul_def, smul_def, mul_left_comm]

instance : SMulCommClass ℂ E (CAt σ) := SMulCommClass.symm _ _ _

end CAt

open CAt

abbrev Fib {E : Type} [Field E] (σ : E →+* ℂ) (V : Type) [AddCommGroup V] [Module E V] : Type :=
  CAt σ ⊗[E] V

section FibSMul

variable {E : Type} [Field E] (σ : E →+* ℂ) (V : Type) [AddCommGroup V] [Module E V]

theorem fib_smul_eq (a : CAt σ) (x : Fib σ V) : a • x = (ofComplex σ).symm a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero]
  | tmul z e => rw [smul_tmul', smul_tmul', complex_smul_def, smul_eq_mul]; rfl
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]

instance (W : Type) [AddCommGroup W] [Module E W] :
    LinearMap.CompatibleSMul (Fib σ V) (Fib σ W) ℂ (CAt σ) where
  map_smul f c x := by
    rw [show c • x = (ofComplex σ c) • x from (fib_smul_eq σ V _ x).symm,
      show c • f x = (ofComplex σ c) • f x from (fib_smul_eq σ W _ (f x)).symm, map_smul]

instance [FiniteDimensional E V] : FiniteDimensional ℂ (Fib σ V) := by
  have : Module.Finite ℂ (CAt σ) := Module.Finite.equiv (ofComplex σ).toLinearEquiv
  exact Module.Finite.trans (CAt σ) (Fib σ V)

end FibSMul

structure MetSpace (E : Type) [Field E] [NumberField E] where

  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module E V]
  [instFD : FiniteDimensional E V]
  [instModuleO : Module (𝓞 E) V]
  [instTower : IsScalarTower (𝓞 E) E V]

  form : ∀ τ : InfinitePlace E, InnerProductSpace.Core ℂ (Fib τ.embedding V)

attribute [instance] MetSpace.instAddCommGroup MetSpace.instModule MetSpace.instFD
  MetSpace.instModuleO MetSpace.instTower

variable {E : Type} [Field E] [NumberField E]

namespace MetSpace

variable (S : MetSpace E)

def FibSp (τ : InfinitePlace E) : Type := Fib τ.embedding S.V

instance (τ : InfinitePlace E) : AddCommGroup (S.FibSp τ) :=
  inferInstanceAs (AddCommGroup (Fib τ.embedding S.V))

instance (τ : InfinitePlace E) : Module ℂ (S.FibSp τ) :=
  inferInstanceAs (Module ℂ (Fib τ.embedding S.V))

instance (τ : InfinitePlace E) : NormedAddCommGroup (S.FibSp τ) :=
  letI : InnerProductSpace.Core ℂ (S.FibSp τ) := S.form τ
  this.toNormedAddCommGroup

instance (τ : InfinitePlace E) : InnerProductSpace ℂ (S.FibSp τ) := InnerProductSpace.ofCore _

instance (τ : InfinitePlace E) : FiniteDimensional ℂ (S.FibSp τ) :=
  inferInstanceAs (FiniteDimensional ℂ (Fib τ.embedding S.V))

def pt (τ : InfinitePlace E) (v : S.V) : S.FibSp τ := (1 : CAt τ.embedding) ⊗ₜ[E] v

theorem inner_at (τ : InfinitePlace E) (v w : S.V) :
    inner ℂ (S.pt τ v) (S.pt τ w) =
      (S.form τ).inner ((1 : CAt τ.embedding) ⊗ₜ[E] v) ((1 : CAt τ.embedding) ⊗ₜ[E] w) := rfl

end MetSpace

variable (E) in

def fPl : ℕ := Fintype.card (InfinitePlace E)

variable (E) in

def rd : ℝ := |(discr E : ℝ)| ^ ((1 : ℝ) / (2 * fPl E))

namespace MetSpace

end MetSpace

namespace MetSpace

variable (S : MetSpace E)

def toSp (τ : InfinitePlace E) : Fib τ.embedding S.V ≃ₗ[ℂ] S.FibSp τ := LinearEquiv.refl ℂ _

def fibSub (W : Submodule E S.V) (τ : InfinitePlace E) : Submodule ℂ (S.FibSp τ) :=
  (LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor (CAt τ.embedding) (CAt τ.embedding)
    (W.subtype.restrictScalars E))).restrictScalars ℂ

def quotEquiv (W : Submodule E S.V) (τ : InfinitePlace E) :
    Fib τ.embedding (S.V ⧸ W) ≃ₗ[ℂ] S.FibSp τ ⧸ S.fibSub W τ :=
  ((TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (CAt τ.embedding) E (CAt τ.embedding)
    W).restrictScalars ℂ).trans (Submodule.Quotient.restrictScalarsEquiv ℂ _).symm

def restrictMap (W : Submodule E S.V) (τ : InfinitePlace E) :
    Fib τ.embedding W →ₗ[ℂ] S.FibSp τ :=
  (W.subtype.baseChange (CAt τ.embedding)).restrictScalars ℂ

end MetSpace

section Lattices

variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

abbrev espan (A : Submodule (𝓞 E) V) : Submodule E V := Submodule.span E (A : Set V)

section Herm

variable {F : Type} [Field F] [Algebra F E] [Algebra.IsQuadraticExtension F E]

def IsSelfDual (h : HermitianForm F E V) (L : Submodule (𝓞 E) V) : Prop :=
  ∀ y : V, y ∈ L ↔ ∀ l ∈ L, h.toSesq y l ∈ Set.range (algebraMap (𝓞 E) E)

end Herm

end Lattices

namespace MetSpace

variable (S : MetSpace E)

def fibMap (T : MetSpace E) (φ : S.V →ₗ[E] T.V) (τ : InfinitePlace E) :
    S.FibSp τ →ₗ[ℂ] T.FibSp τ :=
  ((φ.baseChange (CAt τ.embedding)).restrictScalars ℂ : Fib τ.embedding S.V →ₗ[ℂ] Fib τ.embedding T.V)

end MetSpace

namespace MetSpace

end MetSpace

structure SelfDualFrame (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] where

  S : MetSpace E

  B : HermitianForm F E S.V

  L : Submodule (𝓞 E) S.V
  fg : L.FG
  selfDual : IsSelfDual B L

  θ : ∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S.FibSp τ
  θ_θ : ∀ τ u, θ τ (θ τ u) = u
  θ_isometry : ∀ τ u v, inner ℂ (θ τ u) (θ τ v) = inner ℂ u v
  majorant : ∀ τ (y y' : S.V), inner ℂ (θ τ (S.pt τ y)) (S.pt τ y') = τ.embedding (B.toSesq y y')

namespace SelfDualFrame

end SelfDualFrame

section Standard

variable (E) (n : ℕ)

def stdCoord (σ : E →+* ℂ) : Fib σ (Fin n → E) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  ((piScalarRight E (CAt σ) (CAt σ) (Fin n)).restrictScalars ℂ).trans
    ((LinearEquiv.piCongrRight fun _ ↦ (ofComplex σ).symm.toLinearEquiv).trans
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm)

variable {E n}

theorem stdCoord_tmul (σ : E →+* ℂ) (z : CAt σ) (v : Fin n → E) (i : Fin n) :
    stdCoord E n σ (z ⊗ₜ v) i = σ (v i) * (ofComplex σ).symm z := rfl

variable (E n)

variable {E n}

end Standard

section Frame

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
  [Algebra F E] [Algebra.IsQuadraticExtension F E]

def signs : Fin 2 → Fˣ := ![1, -1]

variable {F}

end Frame

section Frame

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
  [Algebra F E] [Algebra.IsQuadraticExtension F E]

def hypForm : HermitianForm F E (Fin 2 → E) := diagForm (signs F)

theorem hypForm_apply (y y' : Fin 2 → E) :
    (hypForm (F := F) (E := E)).toSesq y y' =
      ∑ i, conj F E (y i) * algebraMap F E (signs F i) * y' i := rfl

end Frame

end

end FunctionalEquationAlt

end GroundTheory.Heights₂.Theta
