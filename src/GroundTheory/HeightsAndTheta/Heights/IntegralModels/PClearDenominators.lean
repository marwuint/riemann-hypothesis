import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PullbackBasis
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.RatLocalAffine
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

section Pull

variable {T Z : Scheme.{0}} (g : T ⟶ Z) (M : Z.Modules)

lemma pullSectionOn_smul (U : Z.Opens) (r : Γ(Z, U)) (m : Γ(M, U)) :
    pullSectionOn g M U (r • m) = g.app U r • pullSectionOn g M U m :=
  Scheme.Modules.Hom.app_smul _ r m

lemma pullSectionOn_res {U V : Z.Opens} (h : V ≤ U) (i : g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ U) (m : Γ(M, U)) :
    pullSectionOn g M V ((M.presheaf.map (homOfLE h).op).hom m) =
      (((Scheme.Modules.pullback g).obj M).presheaf.map i.op).hom (pullSectionOn g M U m) := by
  have := ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).mapPresheaf.naturality
    (homOfLE h).op
  have h2 := congrArg (fun φ => φ.hom m) this
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h2
  rw [Subsingleton.elim i ((Opens.map g.base).map (homOfLE h))]
  exact h2

end Pull

end

end GroundTheory.Heights₂.Heights.Model
