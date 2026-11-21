import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftFormsMainTerm
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookProductPosLogEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsHilbertModuleExists

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open Formalism.L2.Host (HChar ordF atFin IsUnitAt)
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.AdelicLiftCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem chrEq_mul {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
    rfl

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def IsResidual (i : Fin D.R.m) (t : T) (s : ℂ →+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  (∀ PP ∈ R.Pg, m PP = (LiftFormsMainTerm.conjRes s (R.chi ((i : ℕ) + 1)) PP)⁻¹) ∧ ∀ PP ∈ R.Q t, m PP = LiftFormsMainTerm.conjRes s (R.xiR t) PP

variable {R}

variable (R)

variable {R} {F : Face D A}

end GlobalTheory.AdelicLiftCompare

end
