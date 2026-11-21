import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj.SumModel

open GlobalTheory.ChiGrid Formalism.L2.Host Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem readOK {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) : ReadOK σ := by
  obtain ⟨Φ, h, -⟩ := funForm (K := ℂ) σ
  exact readOK_of_equiv σ Φ fun F => (h F _).2 rfl

theorem finEmb_eq {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y : GfC A) (x : GfC B)
    (h : EmbRel B A d.ι x.1 y.1) : finEmb d y = x :=
  Subtype.ext ((GlobalTheory.AutFunCounterexample.embRel_existsUnique B A d.ι d.isom y.1).unique (finEmb_rel d y) h)

theorem finEmb_mul {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y y' : GfC A) :
    finEmb d (y * y') = finEmb d y * finEmb d y' := by
  refine finEmb_eq d _ _ ⟨?_, fun v hv => ?_⟩
  · have h1 := (finEmb_rel d y).1
    have h2 := (finEmb_rel d y').1
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  · have h1 := (finEmb_rel d y).2 v hv
    have h2 := (finEmb_rel d y').2 v hv
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [← Matrix.mulVec_mulVec, h2, h1]

end GlobalTheory.FunObj.SumModel

end
