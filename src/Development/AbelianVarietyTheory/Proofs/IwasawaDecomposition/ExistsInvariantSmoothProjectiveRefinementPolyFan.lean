import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimpLabMinValOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSimplicialLabelledFanRefinement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothRefinementPolyFan

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem GlobalTheory.PolFan.exists_smooth_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ' γ → ψ.LinearOn γ := by
  intro E _ _ _ H q ψ hD hψ hT
  obtain ⟨φ, lab, hφ, hφT, hlT, hSL, hsub⟩ := _root_.GlobalTheory.PolFan.exists_simpLab_refinement E H q ψ hD hψ hT
  obtain ⟨φ', h1, h2, h3, hsub'⟩ := _root_.GlobalTheory.PolFan.resolution E H q φ lab hD hφ hφT hlT hSL
  exact ⟨φ', h1, h2, h3, fun X _ _ _ _ hX m γ hγ => (hsub'.trans hsub).linearOn hX hγ.isCell⟩
