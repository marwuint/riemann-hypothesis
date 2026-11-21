import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelAtOfKnownTheorem

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc

namespace GlobalTheory.SiegLoc

def SiegData (g : ℕ) (φ : InvFun ℤ) (n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n))
    (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S)
    (d N : ℕ) : Prop :=
  IsProjOver s ∧ SmoothOfRelativeDimension (g * (g + 1) / 2) s ∧ j ≫ s = F.s ∧
    (∀ x : S, x ∈ closure (Set.range j ∩ s ⁻¹' {s x})) ∧
    IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j ∧
    1 ≤ d ∧ (∀ x : S, HasChart F s j e φ BD d x) ∧
    1 ≤ N ∧ IsGenerated (lbPow (hodge G g) N) ∧
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (hodge G g) (N * k)) (CechPic.dual BD.lb))

theorem siegAt_iff (g : ℕ) (φ : InvFun ℤ) (n : ℕ) :
    SiegAt g φ n ↔ ∃ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S)
      (_ : IsOpenImmersion j) (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ),
      SiegData g φ n F S s j G e BD d N := Iff.rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

end GlobalTheory.SiegLoc
