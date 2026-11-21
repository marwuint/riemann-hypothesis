import Development.EtaleCohomology.EtaleSheaves.LeafSpreadVCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafDescendVCut

abbrev toR {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) : Sp Ω ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom (algebraMap R Ω))

abbrev incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') : Sp R' ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

def LeafIrred : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), IsCurve c0 →
    SmoothOfRelativeDimension 1 q → IsPullback v0 c0 q (toR R) → IrreducibleSpace D0

def LeafDimBound : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R), SmoothOfRelativeDimension 1 q →
    topologicalKrullDim D0 ≤ ringKrullDim R + 1

end LateralTheory.E.LeafDescendVCut

end
