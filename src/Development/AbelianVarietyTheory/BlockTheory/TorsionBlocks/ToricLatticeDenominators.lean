import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators

section Index

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : Type} [AddCommGroup W] [Module (FractionRing R) W] [Module R W]
  [IsScalarTower R (FractionRing R) W]

def IsLatIn (V : Submodule (FractionRing R) W) (L : Submodule R W) : Prop :=
  L.FG ∧ Submodule.span (FractionRing R) (L : Set W) = V

end Index

section Lattices

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool)

def eOp : Module.End (FractionRing (X.O i)) (Y.Fm i j b) :=
  MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b)) (Y.eAlg i b)

def typePart : Submodule (FractionRing (X.O i)) (Y.Fm i j b) :=
  ⨅ u : Y.U, Module.End.eigenspace
    ((Y.actG i j b u : Y.Fm i j b ≃ₗ[FractionRing (X.O i)] Y.Fm i j b) :
      Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i))

def V0 : Submodule (FractionRing (X.O i)) (Y.Fm i j b) :=
  LinearMap.range (eOp Y i j b) ⊓ typePart Y i j b

def Theta : Submodule (X.O i) (Y.Fm i j b) :=
  Submodule.span (X.O i) (Set.range (Y.th i j b))

variable (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O']

abbrev FmExt : Type := FractionRing O' ⊗[X.O i] Y.Fm i j b

def eExt : FmExt Y i j b O' →ₗ[O'] FmExt Y i j b O' :=
  (((eOp Y i j b).restrictScalars (X.O i)).baseChange (FractionRing O')).restrictScalars O'

variable (k : ℕ) [Algebra (X.Ok i k) O'] [IsScalarTower (X.O i) (X.Ok i k) O']

def incl : X.Ok i k ⊗[X.O i] Y.Fm i j b →ₗ[X.O i] FmExt Y i j b O' :=
  LinearMap.rTensor (Y.Fm i j b)
    ((IsScalarTower.toAlgHom (X.O i) O' (FractionRing O')).comp
      (IsScalarTower.toAlgHom (X.O i) (X.Ok i k) O')).toLinearMap

end Lattices

end GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators

end
