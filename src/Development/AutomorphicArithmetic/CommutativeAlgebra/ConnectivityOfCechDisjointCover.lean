import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem eqv_of_iso {R : Type} [CommRing R] {F : Shv R} {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

end
