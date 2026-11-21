import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombination

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv TanM)
open scoped MonObj
open GlobalTheory.LieMet (tanOf isTan_tv tan_ext pushE left_pushE isTan_map)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.StepBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Transport

variable {X X₁ X₂ : Scheme.{0}} {t : SAB H X} {t₁ : SAB H X₁} {t₂ : SAB H X₂} {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X}
  (m₁ : SABMap t₁ t f₁) (m₂ : SABMap t₂ t f₂) {S : Type} [CommRing S] {x₁ : Sp S ⟶ X₁} {x₂ : Sp S ⟶ X₂}
  (hx : x₁ ≫ f₁ = x₂ ≫ f₂)

include hx in

theorem isComb_corr {n : ℕ} {b₁ : Fin n → (Sp (DualNumber S) ⟶ t₁.G.left)} {b₂ : Fin n → (Sp (DualNumber S) ⟶ t₂.G.left)}
    (h₁ : ∀ j, IsTanAtG t₁ x₁ (b₁ j)) (h₂ : ∀ j, IsTanAtG t₂ x₂ (b₂ j)) (hb : ∀ j, b₁ j ≫ m₁.φ = b₂ j ≫ m₂.φ)
    {w₁ : Sp (DualNumber S) ⟶ t₁.G.left} {w₂ : Sp (DualNumber S) ⟶ t₂.G.left} (k₁ : IsTanAtG t₁ x₁ w₁)
    (k₂ : IsTanAtG t₂ x₂ w₂) (hw : w₁ ≫ m₁.φ = w₂ ≫ m₂.φ) {cf : Fin n → S} (hc : IsCombAtG t₁ x₁ b₁ cf w₁) :
    IsCombAtG t₂ x₂ b₂ cf w₂ := by
  have e := (LieMet.isComb_iff (fun j => tanOf (h₁ j)) cf (tanOf k₁)).1 hc
  refine (LieMet.isComb_iff (fun j => tanOf (h₂ j)) cf (tanOf k₂)).2 ((pushE m₂ x₂ rfl).injective ?_)
  have e₁ : pushE m₂ x₂ rfl (tanOf k₂) = pushE m₁ x₁ hx (tanOf k₁) := tan_ext hw.symm
  have e₂ (j) : pushE m₂ x₂ rfl (tanOf (h₂ j)) = pushE m₁ x₁ hx (tanOf (h₁ j)) := tan_ext (hb j).symm
  rw [e₁, e, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul, e₂]

end Transport

end GlobalTheory.LocM.StepBasis
