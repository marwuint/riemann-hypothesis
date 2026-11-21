import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLInvolutive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.FA
open scoped Classical

attribute [local instance] borelG borelF borelH

namespace GlobalTheory.CompanionTheory.FmPowP

section Generic

variable {H : Type} [Group H]

theorem hint_ind_left (K U : Subgroup H) (hUK : U ≤ K) (hi : U.relIndex K ≠ 0) (f : H → ℂ)
    (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g) (m : H) :
    hint K (fun z => (U : Set H).indicator (fun _ => ((U.relIndex K : ℕ) : ℂ)) z * f (z⁻¹ * m)) = f m := by
  have hC : ((U.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hi
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K U _ hUK (fun k hk x => ?_) hi]
  · rw [finsum_eq_single _ ((1 : H) : H ⧸ U)]
    · have hmem : (((1 : H) : H ⧸ U).out : H) ∈ U := by
        have := QuotientGroup.out_eq' ((1 : H) : H ⧸ U)
        simpa using (QuotientGroup.eq.1 this)
      rw [Set.indicator_of_mem (by exact hmem), hl _ (inv_mem hmem)]
      field_simp
    · intro q hq
      have hnot : (q.out : H) ∉ U := fun h => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa using inv_mem h))
      rw [Set.indicator_of_notMem (by exact hnot), zero_mul]
  · have h1 : (x * k ∈ (U : Set H)) ↔ x ∈ (U : Set H) := Subgroup.mul_mem_cancel_right U hk
    have h2 : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m) := by group
    rw [h2, hl _ (inv_mem hk)]
    by_cases hx : x ∈ (U : Set H)
    · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

theorem hint_ind_right (K U : Subgroup H) (hUK : U ≤ K) (hi : U.relIndex K ≠ 0) (f : H → ℂ)
    (hr : ∀ u ∈ U, ∀ g, f (g * u) = f g) (m : H) :
    hint K (fun z => f z * (U : Set H).indicator (fun _ => ((U.relIndex K : ℕ) : ℂ)) (z⁻¹ * m)) = f m := by
  have hC : ((U.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hi
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K U _ hUK (fun k hk x => ?_) hi]
  · rw [finsum_eq_single _ ((m : H) : H ⧸ U)]
    · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U m
      have hmem : ((((m : H) : H ⧸ U).out : H))⁻¹ * m ∈ U := by
        rw [hu]; simp
      rw [Set.indicator_of_mem (by exact hmem), hu, hr _ u.2]
      field_simp
    · intro q hq
      have hnot : ((q.out : H))⁻¹ * m ∉ U := fun h => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 h)
      rw [Set.indicator_of_notMem (by exact hnot), mul_zero]
  · have h2 : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m) := by group
    have h1 : (k⁻¹ * (x⁻¹ * m) ∈ (U : Set H)) ↔ x⁻¹ * m ∈ (U : Set H) :=
      Subgroup.mul_mem_cancel_left U (inv_mem hk)
    rw [hr _ hk, h2]
    by_cases hx : x⁻¹ * m ∈ (U : Set H)
    · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

theorem relIndex_ne_of_open [TopologicalSpace H] [IsTopologicalGroup H] {K U : Subgroup H}
    (hU : IsOpen (U : Set H)) (hK : IsCompact (K : Set H)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := hU.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem isCompact_maximal_pair_place (w : Pl E) : IsCompact ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
  have h1 := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have h2 := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  simpa [Subgroup.coe_prod] using h1.prod h2

theorem mconv_idem_left {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) (f : LF a b w) (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g) :
    PositivityTheory.Rg.BcN.F2.mconv (idem U) f = f := by
  funext m
  exact hint_ind_left _ U hUK (relIndex_ne_of_open hU (isCompact_maximal_pair_place w)) f hl m

theorem mconv_idem_right {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) (f : LF a b w) (hr : ∀ u ∈ U, ∀ g, f (g * u) = f g) :
    PositivityTheory.Rg.BcN.F2.mconv f (idem U) = f := by
  funext m
  exact hint_ind_right _ U hUK (relIndex_ne_of_open hU (isCompact_maximal_pair_place w)) f hr m

theorem mconv_zero_left {w : Pl E} (f : LF a b w) : PositivityTheory.Rg.BcN.F2.mconv (0 : LF a b w) f = 0 := by
  funext m
  simpa [PositivityTheory.Rg.BcN.F2.mconv] using GlobalTheory.CompanionTheory.FamClP.hint_zero (K2 a b w)

theorem mconv_zero_right {w : Pl E} (f : LF a b w) : PositivityTheory.Rg.BcN.F2.mconv f (0 : LF a b w) = 0 := by
  funext m
  simpa [PositivityTheory.Rg.BcN.F2.mconv] using GlobalTheory.CompanionTheory.FamClP.hint_zero (K2 a b w)

theorem idem_left {w : Pl E} (U : Subgroup (GLw a w × GLw b w)) (u) (hu : u ∈ U) (g) : idem U (u * g) = idem U g := by
  have h1 : (u * g ∈ (U : Set (GLw a w × GLw b w))) ↔ g ∈ (U : Set (GLw a w × GLw b w)) :=
    Subgroup.mul_mem_cancel_left U hu
  unfold idem
  by_cases hx : g ∈ (U : Set (GLw a w × GLw b w))
  · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

section Alg

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

theorem mconv_idem_idem {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) : PositivityTheory.Rg.BcN.F2.mconv (idem U) (idem U) = idem U :=
  mconv_idem_left hU hUK _ (idem_left U)

end Alg

end GlobalTheory.CompanionTheory.FmPowP

end
