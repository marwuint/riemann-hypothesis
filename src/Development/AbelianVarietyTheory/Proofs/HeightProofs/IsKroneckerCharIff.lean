import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LinePeriodExponential
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosKeyArchAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexConjugate

noncomputable section
namespace GlobalTheory.CM.Compare

open GlobalTheory.IndefiniteRowSideFullHecke

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lattice

theorem span_iff {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] {I : Type}
    [Fintype I] {N : I → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module O (N i)] (f : ∀ i, N i →ₗ[O] M) :
    (∃ n : ℕ, 0 < n ∧ ∀ a : M, ∃ x : ∀ i, N i, n • a = ∑ i, f i (x i)) ↔
      ∀ a : M, ∃ n : ℕ, 0 < n ∧ n • a ∈ ⨆ i, LinearMap.range (f i) := by
  classical
  have key : ∀ a : M, a ∈ ⨆ i, LinearMap.range (f i) ↔ ∃ x : ∀ i, N i, a = ∑ i, f i (x i) := fun a => by
    refine ⟨fun h => ?_, ?_⟩
    · refine Submodule.iSup_induction _ (motive := fun a => ∃ x : ∀ i, N i, a = ∑ i, f i (x i)) h ?_ ⟨0, by simp⟩ ?_
      · rintro i _ ⟨b, rfl⟩
        refine ⟨Pi.single i b, ?_⟩
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero]) (by simp),
          Pi.single_eq_same]
      · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, by simp [Finset.sum_add_distrib]⟩
    · rintro ⟨x, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨_, rfl⟩
  simp only [← key]
  refine ⟨fun ⟨n, hn, h⟩ a => ⟨n, hn, h a⟩, fun h => ?_⟩
  choose n hn h using h
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := M)
  refine ⟨∏ a ∈ s, n a, Finset.prod_pos fun a _ => hn a, fun a => ?_⟩
  have : Submodule.span O (s : Set M) ≤
      (⨆ i, LinearMap.range (f i)).comap ((∏ a ∈ s, n a) • (LinearMap.id : M →ₗ[O] M)) :=
    Submodule.span_le.2 fun b hb => by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (show b ∈ s from hb)
      show (∏ a ∈ s, n a) • b ∈ ⨆ i, LinearMap.range (f i)
      rw [hc, mul_comm, mul_smul]
      exact nsmul_mem (h b) c
  exact this (hs ▸ Submodule.mem_top)

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)

def latEquiv (Λ : ℝ) : LogarithmicDifferentialCharacter.LatData hP Λ ≃
    {Z : CMLat hP D.p D.q // 1 ≤ Λ ∧ ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ Λ ^ 2} where
  toFun X := ⟨⟨X.A, X.sigP, X.sigM, X.ψ, X.pure, X.hh, X.form, (haveI := D.fin; span_iff X.ψ).2 X.span⟩,
    X.one_le, X.bound⟩
  invFun Z := ⟨Z.1.D₁, Z.1.sigP, Z.1.sigM, Z.1.f, Z.1.hh, Z.1.pure, Z.1.form,
    (haveI := D.fin; span_iff Z.1.f).1 Z.1.span, Z.2.1, Z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Lattice

variable {K : Type} [Field K] [NumberField K]

end GlobalTheory.CM.Compare
end
