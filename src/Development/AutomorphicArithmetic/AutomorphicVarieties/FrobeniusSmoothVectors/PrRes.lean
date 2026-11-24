module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem residue_eq_map_algebraMap_comp_res_of_isCO {O' C : Type} [CommRing O'] [IsLocalRing O'] [CommRing C] [Algebra O' C]
    [IsCO O' C] [IsLocalHom (algebraMap O' C)] :
    IsLocalRing.residue C =
      (IsLocalRing.ResidueField.map (algebraMap O' C)).comp (res O' C : C →+* ResidueField O') := by
  ext z
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O') z
  have h1 : (res O' C) z = (res O' C) (algebraMap O' C a) := by
    rwa [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
  have h2 : IsLocalRing.residue C z = IsLocalRing.residue C (algebraMap O' C a) := by
    rwa [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  rw [RingHom.comp_apply, RingHom.coe_coe, h1, h2, AlgHom.commutes]
  exact (IsLocalRing.ResidueField.map_residue _ a).symm

private theorem nRep_isBar_of_isBar_comp_map {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {K K' : Type} [Field K] [CommRing K'] [Nontrivial K'] (f : k →+* K) (j : K →+* K')
    (σ : NRep F n K) (h : NRep.IsBar (j.comp f) (NRep.map j σ)) : NRep.IsBar f σ := by
  unfold NRep.IsBar at h ⊢
  exact ⟨fun g i => j.injective (h.1 g i), fun v i g => j.injective (h.2 v i g)⟩

theorem UpperTheory.V.Fr.pr_res :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (∃ φ : ResidueField O →+* ResidueField L.O', (L.ρ.bar L.O').IsBar φ) ∧ ((∀ g, UpT ((L.ρ.bar L.O').r g)) ∨ ∀ g, UpT ((L.ρ.bar L.O').r g)ᵀ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  have hOloc : IsLocalHom (algebraMap O L.O') := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have hm : algebraMap O L.O' a ∈ maximalIdeal L.O' := by
      rw [← L.unr]
      exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr h)
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap L.O' L.R) := IsCO.isLocalHom
  let f0 : ResidueField O →+* ResidueField L.O' := IsLocalRing.ResidueField.map (algebraMap O L.O')
  let jR : ResidueField L.O' →+* ResidueField L.R :=
    IsLocalRing.ResidueField.map (algebraMap L.O' L.R)
  have hloc := loc_rho hF hn S x L
  refine ⟨⟨f0, ?_⟩, ?_⟩
  · have hfR : IsResMap O L.R (jR.comp f0) := by
      intro a
      show jR (f0 (IsLocalRing.residue O a)) = _
      rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
        IsScalarTower.algebraMap_apply O L.O' L.R a]
    have hbR := hloc.2.1 _ hfR
    rw [residue_eq_map_algebraMap_comp_res_of_isCO (O' := L.O') (C := L.R)] at hbR
    exact nRep_isBar_of_isBar_comp_map f0 jR _ hbR
  · by_cases hP : S.u.triP ≤ x
    · left
      have hle : L.ρ.triP ≤ maximalIdeal L.R := by
        rw [(hloc.2.2.1 (maximalIdeal L.R)).1]
        show S.u.triP ≤ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R)
        rwa [L.lies]
      intro g i j hji
      have hm : L.ρ.r g i j ∈ maximalIdeal L.R := by
        refine hle ?_
        unfold NRep.triP
        exact Ideal.subset_span ⟨g, i, j, hji, rfl⟩
      exact (res_eq_zero_iff _ _ _).mpr hm
    · right
      have hle := (hloc.2.2.2 hP).2
      intro g i j hji
      have hm : L.ρ.r g j i ∈ maximalIdeal L.R := by
        refine hle ?_
        unfold NRep.triM
        exact Ideal.subset_span ⟨g, j, i, hji, rfl⟩
      exact (res_eq_zero_iff _ _ _).mpr hm
