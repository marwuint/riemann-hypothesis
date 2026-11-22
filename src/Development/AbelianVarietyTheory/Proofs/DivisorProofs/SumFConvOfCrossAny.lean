import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.DvrAnyChar

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar

theorem qkToAkU_level_any : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n →
    N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, q.y = n • p.y → q.g = p.g →
    QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F N q x := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ _ k n N hk hn hN p q x hy hg hx
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hn
  obtain ⟨x₀, h₀⟩ := existsTransl_any hL R I hI D A G hG U F k hk p
  have a := (indAtTransl_any hL R I hI D A G hG U F k hk p x₀).1
    (h₀ 1 k le_rfl (Nat.mul_one k).symm p (one_nsmul _).symm rfl)
  obtain rfl := GlobalTheory.TorsionImage.qkToAkU_unique hL.1 hL.2.1 R I hI D A G hG U F k hk p x x₀ hx a
  exact (indAtTransl_any hL R I hI D A G hG U F N hN1 q x).1 (h₀ n N hn hN q hy hg)

end GlobalTheory.DvrAnyChar
