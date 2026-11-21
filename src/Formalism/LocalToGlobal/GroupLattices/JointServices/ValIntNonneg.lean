import Formalism.LocalToGlobal.GroupLattices.JointServices
import Formalism.LocalToGlobal.GroupLattices.JointServices.VAddEqVw
import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.DIV Formalism.L2.Indef

noncomputable section

namespace Formalism.L2.G.ServJoint

theorem perCol_lin (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (φ : D.what₂.Mu u) :
    ∃ f : D.what₂.Amb μ →ₗ[ℂ] ℂ, ∀ F, D.what₂.perCol u μ φ F = f F := by
  by_cases h : μ = D.what₂.mu0
  · subst h
    refine ⟨((D.mem u).P.period ((D.mem u).P.lowerMap ((D.mem u).P.evz ((D.mem u).C.col ↑(D.eMu u φ))))).comp
      (D.eMt u).symm.toLinearMap, fun F => ?_⟩
    rw [D.perCol_base_eq_PtilCol]
    rfl
  · refine ⟨((D.PTw u μ).period ((D.PTw u μ).lowerMap ((D.PTw u μ).evz
      ((D.chTw u μ).col (D.e0Tw u μ ↑(D.eMu u φ)))))).comp (D.eMtTw u μ).symm.toLinearMap, fun F => ?_⟩
    rw [D.perCol_tie u μ h]
    rfl

end Formalism.L2.G.ServJoint

end
