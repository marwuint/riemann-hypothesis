import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

theorem IsBasisOn.restrict {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {n : ℕ}
    {s : Fin n → Γ(M, U)} (hs : IsBasisOn M U s) {V : X.Opens} (hVU : V ≤ U) :
    IsBasisOn M V (fun i => (M.presheaf.map (homOfLE hVU).op).hom (s i)) := by
  intro W hWV
  have key : (fun r : Fin n → Γ(X, W) =>
      ∑ i, r i • (M.presheaf.map (homOfLE hWV).op).hom
        ((M.presheaf.map (homOfLE hVU).op).hom (s i))) =
      (fun r : Fin n → Γ(X, W) =>
        ∑ i, r i • (M.presheaf.map (homOfLE (hWV.trans hVU)).op).hom (s i)) := by
    funext r
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    show _ = (M.presheaf.map ((homOfLE hVU).op ≫ (homOfLE hWV).op)).hom (s i)
    rw [Functor.map_comp]
    rfl
  rw [key]
  exact hs W (hWV.trans hVU)

end

end GroundTheory.Heights₂.Heights.Model
