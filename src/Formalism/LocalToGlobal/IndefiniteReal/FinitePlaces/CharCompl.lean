import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix Topology
open scoped TensorProduct ComplexConjugate Pointwise

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

abbrev QO : Type := MO S T ⧸ ratL T S

def chiO (ψ : AddChar (AF D.host.F) ℂ) (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : MO S T) : ℂ :=
  ψ (symplO S T z (ratW T S a))

theorem periodic_of {f : MO S T → ℂ} (hf : ∀ a z, f (ratW T S a + z) = f z) :
    ∀ g ∈ ratL T S, ∀ z, f (g + z) = f z := by
  intro g hg z
  obtain ⟨a, rfl⟩ := (mem_ratL_iff S T g).1 hg
  exact hf a z

theorem chiO_periodic (hψ : IsStdChar D ψ (-1)) (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : MO S T) :
    chiO S T ψ a (ratW T S b + z) = chiO S T ψ a z := by
  unfold chiO
  rw [symplO_add_left, AddChar.map_add_eq_mul, psi_rat hψ, one_mul]

def liftQ (f : MO S T → ℂ) (hf : ∀ a z, f (ratW T S a + z) = f z) : QO S T → ℂ :=
  Quotient.lift f (by
    intro x y hxy
    have h : -x + y ∈ ratL T S := QuotientAddGroup.leftRel_apply.1 hxy
    have := periodic_of S T hf (-x + y) h x
    rw [show -x + y + x = y by abel] at this
    exact this.symm)

theorem cont_liftQ (f : MO S T → ℂ) (hf : ∀ a z, f (ratW T S a + z) = f z) (hc : Continuous f) :
    Continuous (liftQ S T f hf) :=
  hc.quotient_lift _

def liftC (f : MO S T → ℂ) (hf : ∀ a z, f (ratW T S a + z) = f z) (hc : Continuous f) : C(QO S T, ℂ) :=
  ⟨liftQ S T f hf, cont_liftQ S T f hf hc⟩

def chiC (hψ : IsStdChar D ψ (-1)) (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : C(QO S T, ℂ) :=
  liftC S T (chiO S T ψ a) (fun b z => chiO_periodic S T hψ a b z)
    ((psi_cont hψ).comp (cont_symplO_left S T _))

theorem chiC_apply (hψ : IsStdChar D ψ (-1)) (a) (z : MO S T) :
    chiC S T hψ a (z : QO S T) = ψ (symplO S T z (ratW T S a)) := rfl

end Formalism.IndefR.Fin

end
