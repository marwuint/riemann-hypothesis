import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpFrame.GLInhab

variable (l : ℕ) [Fact l.Prime] (N : ℕ)

theorem one_mem_dualWeyl :
    (1 : MvPolynomial (Fin N × Fin N) (PadicAlgCl l)) ∈ Formalism.GradedWeylDivisibility.dualWeyl (PadicAlgCl l) N N (res N (fun _ : ℕ => 0)) := by
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · have h0 : res N (fun _ : ℕ => 0) = 0 := rfl
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule, h0]
    exact MvPolynomial.isWeightedHomogeneous_one (R := PadicAlgCl l) (Formalism.GradedWeylDivisibility.colW N N)
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b _
    simp

def oneVec : NablaT (PadicAlgCl l) N (fun (_ : Unit) (_ : ℕ) => 0) :=
  PiTensorProduct.tprod (PadicAlgCl l) fun _ => ⟨1, one_mem_dualWeyl l N⟩

theorem oneVec_ne_zero : oneVec l N ≠ 0 := by
  intro h
  have h2 := congrArg (PiTensorProduct.subsingletonEquiv (R := PadicAlgCl l)
    (s := fun _ : Unit => Formalism.GradedWeylDivisibility.dualWeyl (PadicAlgCl l) N N (res N (fun _ : ℕ => 0))) ()) h
  rw [oneVec, PiTensorProduct.subsingletonEquiv_apply_tprod, map_zero] at h2
  exact one_ne_zero (congrArg Subtype.val h2)

theorem grp_oneVec (g : Unit → GL (Fin N) (PadicAlgCl l)) :
    grp (PadicAlgCl l) N (fun (_ : Unit) (_ : ℕ) => 0) g (oneVec l N) = oneVec l N := by
  simp only [grp, Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep, oneVec, MonoidHom.coe_comp, Function.comp_apply]
  rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
  congr 1
  funext τ
  apply Subtype.ext
  simp [Formalism.UG.dualWeylRep_apply]

end GlobalTheory.ExpFrame.GLInhab

namespace GlobalTheory.ExpFrame

end GlobalTheory.ExpFrame
