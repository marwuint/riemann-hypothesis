import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.EigenLatticeFrames
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsTriangularReframeExistsAndUnique
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntFramesCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames GlobalTheory.Reg

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Basis

variable {S : Type} [Field S] [Algebra c.F S] {x : Sp S ⟶ Xo.X} {τ : E →+* ℂ}
  {u v : Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}

theorem exists_eigenBasisAt (hx0 : x ≫ Xo.s = sOf c S) (τ : E →+* ℂ) : ∃ u, IsEigenBasisAt Xo c x τ u := by
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  let B : Module.Basis (Fin (Dw.mult τ)) S (gfpEig (c := c) hx τ) :=
    Module.finBasisOfFinrankEq S _ (gfp_finrank hx0 hx τ)
  have hd : LinearIndependent S ((gfpEig (c := c) hx τ).subtype ∘ B) :=
    B.linearIndependent.map' (gfpEig (c := c) hx τ).subtype (Submodule.ker_subtype _)
  have hW : ∀ i, ((gfpEig (c := c) hx τ).subtype ∘ B) i ∈ gfpEig (c := c) hx τ := fun i => (B i).2
  exact ⟨fun i => gfpVec x xc (((gfpEig (c := c) hx τ).subtype ∘ B) i), fun i => gfp_tan hx _,
    fun i => (gfp_eig_iff hx τ _).2 (hW i), fun w hw he => gfp_basis hx0 hx τ _ hd hW w hw he⟩

end Basis

variable (Xo c)

end GlobalTheory.IntFramesCompare
