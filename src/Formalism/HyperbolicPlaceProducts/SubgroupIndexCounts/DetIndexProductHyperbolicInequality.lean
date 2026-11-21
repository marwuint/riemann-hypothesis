import Formalism.HyperbolicPlaceProducts.DetIndexProductHyperbolicInequality

open Module

noncomputable section

namespace Formalism.SLP.GlobalBoundRefinements.P

open Formalism.SLP.GlobalBoundRefinements

theorem card_linearEquiv_le : Formalism.SLP.GlobalBoundRefinements.AutCount := by
  intro R M _ _ _ _ e v hv
  have hinj : Function.Injective (fun f : M ≃ₗ[R] M => fun i => f (v i)) := by
    intro f g hfg
    apply LinearEquiv.toLinearMap_injective
    exact LinearMap.ext_on_range hv (fun i => congrFun hfg i)
  calc Nat.card (M ≃ₗ[R] M) ≤ Nat.card (Fin e → M) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card M ^ e := by rw [Nat.card_fun, Nat.card_fin]

end Formalism.SLP.GlobalBoundRefinements.P
