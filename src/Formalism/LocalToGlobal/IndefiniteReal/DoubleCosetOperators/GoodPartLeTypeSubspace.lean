import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose

noncomputable section

open NumberField TensorProduct

namespace Formalism.IndefR.NX.Core

structure RatCore where
  L0 : Type
  [fieldBase : Field L0]
  [numberFieldBase : NumberField L0]
  Ks : Type
  [fKs : Field Ks]
  [nfKs : NumberField Ks]
  [algKs : Algebra Ks L0]

  Tw : Type
  O : Tw → Type
  [crO : ∀ i, CommRing (O i)]
  [domO : ∀ i, IsDomain (O i)]

  fractionRingMaps : ∀ (i : Tw) (_b : Bool), L0 →+* FractionRing (O i)

  G : Type
  [grpG : Group G]
  [finG : Fintype G]
  WL : ℕ → Type
  [acgWL : ∀ j, AddCommGroup (WL j)]
  [modWL : ∀ j, Module L0 (WL j)]
  [modKsWL : ∀ j, Module Ks (WL j)]
  [towWL : ∀ j, IsScalarTower Ks L0 (WL j)]
  [modOLWL : ∀ j, Module (𝓞 L0) (WL j)]
  [towOLWL : ∀ j, IsScalarTower (𝓞 L0) L0 (WL j)]
  [modOKsWL : ∀ j, Module (𝓞 Ks) (WL j)]
  [towOKsWL : ∀ j, IsScalarTower (𝓞 Ks) Ks (WL j)]
  W : ℕ → (L0 →+* ℂ) → Type
  [nW : ∀ j σ, NormedAddCommGroup (W j σ)]
  [ipW : ∀ j σ, InnerProductSpace ℂ (W j σ)]

  A : ∀ j, Arith.FormsL L0 Ks (WL j) (W j) G

attribute [instance] RatCore.fieldBase RatCore.numberFieldBase RatCore.fKs RatCore.nfKs RatCore.algKs RatCore.crO RatCore.domO
  RatCore.grpG RatCore.finG RatCore.acgWL RatCore.modWL RatCore.modKsWL RatCore.towWL RatCore.modOLWL
  RatCore.towOLWL RatCore.modOKsWL RatCore.towOKsWL RatCore.nW RatCore.ipW

variable (C : RatCore)

def KB (_C : RatCore) (i : _C.Tw) (_b : Bool) : Type := FractionRing (_C.O i)

instance (i : C.Tw) (b : Bool) : Field (KB C i b) := inferInstanceAs (Field (FractionRing (C.O i)))

def rd (i : C.Tw) (b : Bool) : C.L0 →+* KB C i b := C.fractionRingMaps i b

def ιK (i : C.Tw) (b : Bool) : C.Ks →+* KB C i b := (rd C i b).comp (algebraMap C.Ks C.L0)

instance (i : C.Tw) (b : Bool) : Algebra C.Ks (KB C i b) := (ιK C i b).toAlgebra

def FmK (j : ℕ) : Type := ↥(C.A j).WK

instance (j : ℕ) : AddCommGroup (FmK C j) := inferInstanceAs (AddCommGroup ↥(C.A j).WK)

instance (j : ℕ) : Module C.Ks (FmK C j) := inferInstanceAs (Module C.Ks ↥(C.A j).WK)

def Fm (i : C.Tw) (j : ℕ) (b : Bool) : Type := KB C i b ⊗[C.Ks] FmK C j

instance acgFm (i : C.Tw) (j : ℕ) (b : Bool) : AddCommGroup (Fm C i j b) :=
  inferInstanceAs (AddCommGroup (KB C i b ⊗[C.Ks] FmK C j))

instance modKB (i : C.Tw) (j : ℕ) (b : Bool) : Module (KB C i b) (Fm C i j b) :=
  inferInstanceAs (Module (KB C i b) (KB C i b ⊗[C.Ks] FmK C j))

instance modFmK (i : C.Tw) (j : ℕ) (b : Bool) : Module (FractionRing (C.O i)) (Fm C i j b) := modKB C i j b

instance modFmO (i : C.Tw) (j : ℕ) (b : Bool) : Module (C.O i) (Fm C i j b) :=
  Module.compHom (Fm C i j b) (algebraMap (C.O i) (FractionRing (C.O i)))

instance towFm (i : C.Tw) (j : ℕ) (b : Bool) : IsScalarTower (C.O i) (FractionRing (C.O i)) (Fm C i j b) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

end Formalism.IndefR.NX.Core
