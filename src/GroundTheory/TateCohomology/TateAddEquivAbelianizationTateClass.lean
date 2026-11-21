import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupHomology TensorProduct Finsupp

universe u

section Tate

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep k G)

noncomputable def tateNegTwoIsoH1 : tateCohomology A (-2) ≅ H1 A :=
  (TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A

variable [A.IsTrivial]

end Tate

end GroundTheory.GroupCoh
