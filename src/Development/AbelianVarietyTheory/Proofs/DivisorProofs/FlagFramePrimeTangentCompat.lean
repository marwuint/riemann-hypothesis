import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HtGen.FlagPoint

open GlobalTheory.LineNorm.Chart GlobalTheory.LieMet

theorem chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    {t : SAB H X} {S G : Scheme.{0}} (j : G ⟶ S) (ρ' : S ⟶ X) {K : Type} [Field K] (O : ValuationSubring K)
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (io : K →+* C) (ioO : O →+* intO C)
    (hio : (intO C).subtype.comp ioO = io.comp O.subtype) (z : Sp K ⟶ G) (yt : Sp O ⟶ S)
    (hyt : spMap O.subtype ≫ yt = z ≫ j) {U : S.Opens} (hU : IsAffineOpen U) (hin : ⊤ ≤ yt ⁻¹ᵁ U) {g m : ℕ}
    (e : Fin g → (Sp (DualNumber Γ(S, U)) ⟶ t.G.left)) (α : Γ(S, U) →+* G.presheaf.stalk (below z))
    (hα : spMap α ≫ hU.fromSpec = G.fromSpecStalk (below z) ≫ j) (a : Fin m → Fin g → G.presheaf.stalk (below z))
    (w : Fin m → (Sp (DualNumber (G.presheaf.stalk (below z))) ⟶ t.G.left))
    (ha : ∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (w l))
    (ψ : G.presheaf.stalk (below z) →+* C) (hψ : ψ = io.comp (Scheme.stalkClosedPointTo z).hom) :
    ∃ β : Γ(S, U) →+* intO C, spMap β ≫ hU.fromSpec = spMap ioO ≫ yt ∧ (∀ r, ψ (α r) = β r) ∧
      ∀ l, IsCombAtG t (spMap (intO C).subtype ≫ (spMap ioO ≫ yt) ≫ ρ')
        (fun i => spMap (dualMap (intO C).subtype) ≫ spMap (dualMap β) ≫ e i) (fun i => ψ (a l i))
        (spMap (dualMap ψ) ≫ w l) := by
  obtain ⟨β, hβ⟩ := exists_ringHom hU yt hin
  obtain ⟨σ, hσ₀⟩ : ∃ σ : G.presheaf.stalk (below z) →+* K, σ = (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  have hσ : σ.comp α = O.subtype.comp β := ringHom_ext hU (by
    rw [← spMap_comp', ← spMap_comp', Category.assoc, Category.assoc, hα, hβ, hyt, ← Category.assoc, hσ₀]
    exact congrArg (· ≫ j) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z))
  have h1 : spMap (ioO.comp β) ≫ hU.fromSpec = spMap ioO ≫ yt := by
    rw [← spMap_comp', Category.assoc, hβ]
  have h2 : ψ.comp α = (intO C).subtype.comp (ioO.comp β) := by
    rw [hψ, ← hσ₀, RingHom.comp_assoc, hσ, ← RingHom.comp_assoc, ← hio, RingHom.comp_assoc]
  refine ⟨ioO.comp β, h1, fun r => congrArg (fun φ => φ r) h2, fun l => ?_⟩
  have := coord_map α ψ (ha l)
  rw [h2, ← spMap_comp', Category.assoc, ← Category.assoc (spMap (ioO.comp β)), h1] at this
  simpa only [dual_comp] using this

end GlobalTheory.HtGen.FlagPoint
