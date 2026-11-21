import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameBlockPermSign
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameSwapNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPerm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XSubXDvdOfRenameSwapEqNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernDvdOfDifferencesDvdStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRoots
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmChern

theorem antisymm_eq_chernRoots_mul_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ), ∃ R : MvPolynomial (ι × ℕ) ℝ, antisymm Q = chernRoots m R * rootDiscr m := by
  intro ι _ m Q
  classical
  obtain ⟨S, hS⟩ : rootDiscr m ∣ antisymm Q := GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd ι m (antisymm Q) fun τ i j hij =>
    _root_.GlobalTheory.swap_odd_dvd (⟨τ, i⟩ : Root m) ⟨τ, j⟩ (by simp [hij.ne]) _ (_root_.GlobalTheory.AntisymmSwap.rename_swap_antisymm ι m Q τ i j hij.ne)
  have hsym : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S := by
    intro w
    have h1 := _root_.GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight ι m Q w
    rw [hS, map_mul, _root_.GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr ι m w, smul_mul_assoc] at h1
    have hs : ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) ≠ 0 := Units.ne_zero _
    exact mul_left_cancel₀ (_root_.GlobalTheory.GoodMetric.rootDiscr_ne_zero ι m) (smul_right_injective _ hs h1)
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric ι m S hsym
  exact ⟨R, by rw [hS, hR, mul_comm]⟩

end GlobalTheory.AntisymmChern
