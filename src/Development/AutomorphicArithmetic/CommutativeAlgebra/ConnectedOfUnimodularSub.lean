import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory

variable (D : Type) [CommRing D] (d : ℕ)

private abbrev Sm (X : RF) (p : ℕ) (T : Scheme.{0}) : Type :=
  {x : Fin (p + 1) → X.obj Γ(T, ⊤) // ∀ i j, X.rel (x i) (x j)}

private theorem eqv_iso {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := by
  intro n
  refine (Function.bijective_iff_has_inverse).2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

end UpperTheory

