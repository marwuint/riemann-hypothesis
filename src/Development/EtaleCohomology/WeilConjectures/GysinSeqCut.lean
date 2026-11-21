import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.Gys

def Good (l r : ℕ) {X Z U : Scheme.{0}} (ι : Z ⟶ X) (j : U ⟶ X) : Prop :=
  IsClosedImmersion ι ∧ IsOpenImmersion j ∧ Set.range j = (Set.range ι)ᶜ ∧
  ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (e : ℕ) (p : X ⟶ Sp Ω), (l : Ω) ≠ 0 ∧
    SmoothOfRelativeDimension (e + r) p ∧ SmoothOfRelativeDimension e (ι ≫ p)

structure SPair (l r : ℕ) where
  (X Z U : Scheme.{0})
  (ι : Z ⟶ X)
  (j : U ⟶ X)
  good : Good l r ι j

structure SPair.Hom {l r : ℕ} (P' P : SPair l r) where
  (fX : P'.X ⟶ P.X)
  (fZ : P'.Z ⟶ P.Z)
  (fU : P'.U ⟶ P.U)
  etale : Etale fX
  sqZ : IsPullback fZ P'.ι P.ι fX
  sqU : fU ≫ P.j = P'.j ≫ fX

section Lim
variable (l : ℕ) [Fact l.Prime]

structure Tower (E : Spc) (n i : ℤ) (E' : Spc) (n' i' : ℤ) where
  app : ∀ c : ℕ, Ht (l ^ c) E n i →+ Ht (l ^ c) E' n' i'
  comm : ∀ c x, red (l ^ (c + 1)) (l ^ c) E' n' i' (app (c + 1) x) = app c (red (l ^ (c + 1)) (l ^ c) E n i x)

variable {l} {E E' : Spc} {n i n' i' : ℤ}

def Tower.hl (u : Tower l E n i E' n' i') : Hl l E n i →ₗ[ℤ_[l]] Hl l E' n' i' where
  toFun x := ⟨fun c => u.app c (x.1 c), fun c => (u.comm c _).trans (congrArg _ (x.2 c))⟩
  map_add' x y := Subtype.ext (funext fun c => map_add (u.app c) (x.1 c) (y.1 c))
  map_smul' r x := Subtype.ext (funext fun c =>
    ((congrArg (u.app c) (HtL.smul_eq l c c le_rfl E n i r (x.1 c))).trans (map_nsmul (u.app c) _ _)).trans
      (HtL.smul_eq l c c le_rfl E' n' i' r (u.app c (x.1 c))).symm)

variable (l) in

def Tower.pull (f : E ⟶ E') (n i : ℤ) : Tower l E' n i E n i := ⟨fun _ => GlobalTheory.EtC.pull _ f _ n, fun _ x => (pull_red _ _ f n i x).symm⟩

end Lim

end LateralTheory.EWeil.Gys

end
