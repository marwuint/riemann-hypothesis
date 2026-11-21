import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJClassFin
import Formalism.PeriodIntegrals.UJClassMassAlt
import Mathlib
import Formalism.HermitianLattices.StatementMass
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.AdelicBounds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.LatticeClassesFiniteRefinement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.PosDefOfDefiniteSignatureHolds

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_sig_ne (D : D7) : ∃ θ : D.host.E, D.sp.cm.sig θ ≠ θ := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers D.host.E)
  obtain ⟨θ, t, e, h⟩ := D.sp.cm.cmUnram.2.2 P hP
  refine ⟨algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ, fun h' => h ?_⟩
  have h'' : star (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ) =
      algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ := h'
  rw [h''] at e
  have : t = θ := NumberField.RingOfIntegers.coe_injective e
  rw [this, sub_self]
  exact P.zero_mem

theorem classFin_of_UJ (hF : PI.UJClassFin.UJClassFin) (D : D7) : ClassFin D := by
  intro W hW hsig
  exact hF D.host.F D.host.E D.sp.cm.sig W.rank W.gram (L0c D W) (fun _ => rfl)
    (fun τ => D.sp.cm.cmUnram.2.1 τ) (fun τ => by have h1 := hW τ; rw [hsig τ] at h1; exact h1)
    (StabFin.crd_up (F := D.host.F) W) (StabFin.crd_low (F := D.host.F) W)

theorem class_number_finite (D : D7) : ClassFin D := classFin_of_UJ unitary_class_set_finite D

theorem class_number_finite_rank (D : D7) (n : ℕ) : ClassFinAt D n := classFinAt_of D (class_number_finite D) n

theorem class_mass_of_genus_classes (hM : PI.UJClassMass2.UJClassMass) (D : D7) : ClassMass D := by
  intro W hW hsig n g hcov hdisj
  exact hM D.host.F D.host.E D.sp.cm.sig W.V W.hT W.rank W.frame W.L0 (fun _ => rfl) (exists_sig_ne D)
    (fun τ => D.sp.cm.cmUnram.2.1 τ) W.herm W.nondeg W.standardTuple_isLattice
    (fun τ => by have h1 := hW τ; rw [hsig τ] at h1; exact h1) n g hcov hdisj

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
