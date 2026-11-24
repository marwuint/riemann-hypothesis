module

public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HarishChandraLabels.Basics
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory ReciprocityTheory.Ty.Fin PI.GreenHCLabel

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin

theorem nonempty_iso_iff_intertwiner {Γ : Type} [Group Γ] (τ σ : FDRep ℂ Γ) :
    Nonempty (τ ≅ σ) ↔ ∃ e : τ ≃ₗ[ℂ] σ, ∀ γ v, e (τ.ρ γ v) = σ.ρ γ (e v) := by
  constructor
  · rintro ⟨i⟩
    refine ⟨FDRep.isoToLinearEquiv i, fun γ v => ?_⟩
    rw [FDRep.Iso.conj_ρ i γ, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  · rintro ⟨e, he⟩
    have h1 : ∀ g, e.toLinearMap ∘ₗ τ.ρ g = σ.ρ g ∘ₗ e.toLinearMap :=
      fun g => LinearMap.ext fun v => he g v
    have h2 : ∀ g, e.symm.toLinearMap ∘ₗ σ.ρ g = τ.ρ g ∘ₗ e.symm.toLinearMap := by
      intro g
      refine LinearMap.ext fun v => ?_
      show e.symm (σ.ρ g v) = τ.ρ g (e.symm v)
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    refine ⟨{ hom := basicsMk e.toLinearMap h1
              inv := basicsMk e.symm.toLinearMap h2
              hom_inv_id := ?_
              inv_hom_id := ?_ }⟩
    · ext v
      simp [basicsMk]
    · ext v
      simp [basicsMk]

private theorem simple_iff_isIrr {Γ : Type} [Group Γ] (τ : FDRep ℂ Γ) :
    CategoryTheory.Simple τ ↔ ReciprocityTheory.Ty.Fin.IsIrr τ.ρ := by
  constructor
  · intro hs
    refine ⟨?_, fun W hW => ?_⟩
    · by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      apply Simple.not_isZero τ
      rw [Limits.IsZero.iff_id_eq_zero]
      apply basics_hom_ext
      rw [basics_lin_id, basics_lin_zero]
      exact LinearMap.ext fun v => @Subsingleton.elim _ hnt _ _
    · haveI hmono : Mono (basicsIncl τ W hW) :=
        basics_mono_of_inj _ (fun x y hxy => Subtype.ext hxy)
      rcases eq_or_ne (basicsIncl τ W hW) 0 with h0 | h0
      · left
        rw [Submodule.eq_bot_iff]
        intro w hw
        have h1 : basicsLin (basicsIncl τ W hW) (⟨w, hw⟩ : W) = w := rfl
        have h2 := congrArg (fun f => basicsLin f (⟨w, hw⟩ : W)) h0
        simp only [basics_lin_zero, LinearMap.zero_apply] at h2
        rwa [← h1]
      · right
        haveI hiso : IsIso (basicsIncl τ W hW) :=
          (Simple.mono_isIso_iff_nonzero (basicsIncl τ W hW)).mpr h0
        rw [eq_top_iff]
        intro v _
        have h3 : basicsLin (inv (basicsIncl τ W hW) ≫ basicsIncl τ W hW) v = v := by
          rw [IsIso.inv_hom_id, basics_lin_id]
          rfl
        rw [basics_lin_comp] at h3
        rw [← h3]
        exact (basicsLin (inv (basicsIncl τ W hW)) v).2
  · rintro ⟨hnt, hirr⟩
    refine ⟨fun {Y} f hf => ⟨fun hiso h0 => ?_, fun h0 => ?_⟩⟩
    · subst h0
      have h1 : 𝟙 τ = 0 := by
        rw [← IsIso.inv_hom_id (0 : Y ⟶ τ), Limits.comp_zero]
      have h2 : basicsLin (𝟙 τ) = 0 := by
        rw [h1, basics_lin_zero]
      rw [basics_lin_id] at h2
      obtain ⟨⟨x, y, hxy⟩⟩ := hnt
      apply hxy
      have hx := LinearMap.congr_fun h2 x
      have hy := LinearMap.congr_fun h2 y
      simp only [LinearMap.id_apply, LinearMap.zero_apply] at hx hy
      rw [hx, hy]
    · have hinj := basics_inj_of_mono f
      have hinv : ∀ g : Γ, ∀ v ∈ LinearMap.range (basicsLin f),
          τ.ρ g v ∈ LinearMap.range (basicsLin f) := by
        rintro g v ⟨y, rfl⟩
        exact ⟨Y.ρ g y, LinearMap.congr_fun (basics_lin_comm f g) y⟩
      rcases hirr _ hinv with hbot | htop
      · exfalso
        apply h0
        apply basics_hom_ext
        rw [basics_lin_zero]
        exact LinearMap.range_eq_bot.mp hbot
      · have hsurj : Function.Surjective (basicsLin f) := LinearMap.range_eq_top.mp htop
        let e := LinearEquiv.ofBijective (basicsLin f) ⟨hinj, hsurj⟩
        have hcomm : ∀ g : Γ, e.symm.toLinearMap ∘ₗ τ.ρ g = Y.ρ g ∘ₗ e.symm.toLinearMap := by
          intro g
          refine LinearMap.ext fun v => ?_
          show e.symm (τ.ρ g v) = Y.ρ g (e.symm v)
          apply e.injective
          rw [LinearEquiv.apply_symm_apply]
          show τ.ρ g v = basicsLin f (Y.ρ g (e.symm v))
          rw [← LinearMap.comp_apply (basicsLin f), basics_lin_comm f g, LinearMap.comp_apply]
          congr 1
          exact (e.apply_symm_apply v).symm
        refine ⟨⟨basicsMk e.symm.toLinearMap hcomm, ?_, ?_⟩⟩
        · apply basics_hom_ext
          rw [basics_lin_comp, basics_lin_id]
          exact LinearMap.ext fun y => e.symm_apply_apply y
        · apply basics_hom_ext
          rw [basics_lin_comp, basics_lin_id]
          exact LinearMap.ext fun v => e.apply_symm_apply v

theorem simpleIffIrr : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by
  unfold ReciprocityTheory.Ty.Fin.St.SimpleIffIrr
  exact ⟨fun Γ _ _ τ => simple_iff_isIrr τ, fun Γ _ _ τ σ => nonempty_iso_iff_intertwiner τ σ⟩

end GlobalTheory.CompanionTheory.TyFin
