import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

namespace UpperTheory.Reformulated.B.Qe28

open NumberField ReciprocityTheory.ChartRestriction.G.FD

@[reducible] noncomputable def FDSec {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r : ℕ} {Comp : Type} (X : Comp → Data E r) : Type :=
  (c : Comp) → Frame (X c).Ψ r → ℂ

noncomputable def IsHolCusp {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r : ℕ} {Comp : Type} (X : Comp → Data E r) (la : (c : Comp) → Wt (X c).Ψ r)
    (P : FDSec X) : Prop :=
  ∀ c, P c ∈ (X c).SS (la c)

noncomputable def holSub {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r : ℕ} {Comp : Type} (X : Comp → Data E r) (la : (c : Comp) → Wt (X c).Ψ r) :
    Submodule ℂ (FDSec X) :=
  Submodule.span ℂ {P | IsHolCusp X la P}

theorem holSub_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (h5 : SiegelSpaceAlgebra (E := E)) {Comp : Type} {X : Comp → Data E r}
    {la la' : (c : Comp) → Wt (X c).Ψ r} {P Q : FDSec X}
    (hP : P ∈ holSub X la) (hQ : Q ∈ holSub X la') :
    P * Q ∈ holSub X (la + la') := by
  have key : ∀ (l : (k : Comp) → Wt (X k).Ψ r) (R : FDSec X),
      R ∈ holSub X l → IsHolCusp X l R := by
    intro l R hR
    induction hR using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact fun c => (h5 r (X c) (l c) (l c) 0).1.1
    | add x y _ _ hx hy => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.1 _ (hx c) _ (hy c)
    | smul a x _ hx => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.2 a _ (hx c)
  exact Submodule.subset_span fun c =>
    (h5 r (X c) (la c) (la' c) 0).2.1 _ (key la P hP c) _ (key la' Q hQ c).1

end UpperTheory.Reformulated.B.Qe28
