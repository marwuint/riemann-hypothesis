import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomIdPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLiftAlongNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.AbDual GlobalTheory.AbLaw
  GlobalTheory.CechPic GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSBijection

open TrivSqZeroExt

section Crystal

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem fst_surj : Function.Surjective (fstHom R R R).toRingHom := fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩

def Comp (d : Crys (epsDP R) (DeRham.epsRed R) A) (f k : HdR A) : Prop :=
  ∀ c : primDR A, d ((constMor A).pull c) = TrivSqZeroExt.inl (f c) + TrivSqZeroExt.inr (k c)

variable {d d' : Crys (epsDP R) (DeRham.epsRed R) A} {f f' k k' : HdR A}

theorem Comp.unique (h : Comp d f k) (h' : Comp d f' k') : f = f' ∧ k = k' :=
  ⟨LinearMap.ext fun c ↦ by simpa using congrArg TrivSqZeroExt.fst ((h c).symm.trans (h' c)),
    LinearMap.ext fun c ↦ by simpa using congrArg TrivSqZeroExt.snd ((h c).symm.trans (h' c))⟩

theorem Comp.add (h : Comp d f k) (h' : Comp d' f' k') : Comp (d + d') (f + f') (k + k') := fun c ↦ by
  rw [LinearMap.add_apply, h, h']
  ext <;> simp

theorem Comp.smul (h : Comp d f k) (r : DualNumber R) : Comp (r • d) (r.fst • f) (r.fst • k + r.snd • f) :=
  fun c ↦ by
  rw [LinearMap.smul_apply, h]
  ext <;> simp [mul_comm]

theorem Comp.ext (hm : (constMor A).IsBC) (h : Comp d f k) (h' : Comp d' f k) : d = d' :=
  JetIsotropic.ext_of_isBC hm fun c ↦ (h c).trans (h' c).symm

variable [IsCommMonObj A] {O : Type} [CommRing O] {a : OAct O A} (hL : LieExact A)

variable (κ : Fil A →ₗ[R] Serre.Lie a)

end Crystal

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {𝔠 : FracId F} {R : Type} [CommRing R]
  {X : Obj F 𝔠 (Sp R)}

end GlobalTheory.KSBijection
