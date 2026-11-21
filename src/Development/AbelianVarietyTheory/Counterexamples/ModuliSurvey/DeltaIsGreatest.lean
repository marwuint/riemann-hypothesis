import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.RealCase
open ReciprocityTheory.ChartRestriction.G.Out Classical
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

variable {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem exists_chart (χ : u.D.toPre.X) : ∃ j : PUnit → u.D.toPre.P.L.ι,
    ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U (j PUnit.unit) := by
  obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart u.D.toPre.P.isLB
    ((u.D.toPre.c χ).left (IsLocalRing.closedPoint u.V))
  refine ⟨fun _ => i, fun x _ => ?_⟩
  rw [Scheme.Hom.mem_preimage]
  exact ((IsLocalRing.specializes_closedPoint (R := u.V) x).map
    (u.D.toPre.c χ).left.continuous).mem_open (u.D.toPre.P.L.U i).isOpen hi

theorem psiNorm_unique (χ : u.D.toPre.X) {r r' : ℝ} (h : u.PsiNorm χ r) (h' : u.PsiNorm χ r') : r = r' := by
  obtain ⟨j, hj⟩ := exists_chart u χ
  exact (h j hj).symm.trans (h' j hj)

end GlobalTheory.ZH.RealCase
end
