module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem mem_PL {l : ℕ} {Γ : Type} [Group Γ] [TopologicalSpace Γ] {H : Subgroup Γ} {x : Γ} :
    x ∈ PL (l := l) H ↔ ∀ U : OpenNormalSubgroup Γ, (∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U) → x ∈ U.toSubgroup := by
  simp only [PL, Subgroup.mem_iInf]

private theorem pq_iff (l : ℕ) (G : Type) [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup l (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ l ^ k ∈ N := by
  refine ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

private theorem exists_core {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K P : Subgroup Γ) [P.Normal] (hK : IsOpen (K : Set Γ)) (hP : P ≤ K) :
    ∃ U : OpenNormalSubgroup Γ, P ≤ U.toSubgroup ∧ U.toSubgroup ≤ K := by
  have : Finite (Γ ⧸ K) := K.quotient_finite_of_isOpen hK
  have : K.FiniteIndex := K.finiteIndex_of_finite_quotient
  have hKc : IsClosed (K : Set Γ) := OpenSubgroup.isClosed ⟨K, hK⟩
  have hCo : IsOpen (K.normalCore : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (K.normalCore_isClosed hKc)
  let C : OpenNormalSubgroup Γ :=
    { toOpenSubgroup := ⟨K.normalCore, hCo⟩
      isNormal' := K.normalCore_normal }
  exact ⟨C, Subgroup.normal_le_normalCore.mpr hP, K.normalCore_le⟩

theorem UpperTheory.V.Pa.pl_props :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ]
      [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
      (H : Subgroup Γ) [H.Normal], IsOpen (H : Set Γ) →
      (PL (l := l) H).Normal ∧ IsClosed (PL (l := l) H : Set Γ) ∧ PL (l := l) H ≤ H ∧
      (∀ U : OpenNormalSubgroup Γ, PL (l := l) H ≤ U.toSubgroup ↔ ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U) ∧
      (PL (l := l) H = ⊥ ↔ IsProL l H) ∧ PL (l := l) H = proLResOf l H := by
  intro l _ Γ _ _ _ _ _ H _ hHo
  have hHc : IsClosed (H : Set Γ) := OpenSubgroup.isClosed ⟨H, hHo⟩
  have cond_le : ∀ U : OpenNormalSubgroup Γ, (∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U) →
      PL (l := l) H ≤ U.toSubgroup :=
    fun U hU x hx => mem_PL.mp hx U hU
  have hnorm : (PL (l := l) H).Normal :=
    ⟨fun x hx g => mem_PL.mpr fun U hU => U.isNormal'.conj_mem _ (mem_PL.mp hx U hU) g⟩
  have hclosed : IsClosed (PL (l := l) H : Set Γ) := by
    simp only [PL, Subgroup.coe_iInf]
    exact isClosed_iInter fun U => isClosed_iInter fun _ => U.toOpenSubgroup.isClosed
  let HU : OpenNormalSubgroup Γ := { toOpenSubgroup := ⟨H, hHo⟩, isNormal' := inferInstance }
  have hle : PL (l := l) H ≤ H := by
    have hc : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ HU := by
      intro h hh
      refine ⟨0, ?_⟩
      rwa [pow_zero, pow_one]
    exact cond_le HU hc
  have hPn : (proLResOf l H).Normal := by
    constructor
    intro x hx g
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    let c : H →* H := (MulAut.conjNormal g).toMonoidHom
    have hc : Continuous c := by
      apply Continuous.subtype_mk
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    refine Subgroup.mem_map.mpr ⟨c y, mem_proLRes.mpr ?_, ?_⟩
    · intro N hN
      let M : OpenNormalSubgroup H :=
        { toSubgroup := N.toSubgroup.comap c
          isOpen' := N.isOpen.preimage hc
          isNormal' := Subgroup.Normal.comap N.isNormal' c }
      have hM : IsPGroup l (H ⧸ M.toSubgroup) := by
        rw [pq_iff] at hN ⊢
        intro z
        obtain ⟨k, hk⟩ := hN (c z)
        exact ⟨k, by simpa [M, map_pow] using hk⟩
      exact mem_proLRes.mp hy M hM
    · simp [c, MulAut.conjNormal_apply]
  have hPc : IsClosed (proLResOf l H : Set Γ) := by
    unfold proLResOf
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact hHc.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_proLRes l H)
  have hPcond (U : OpenNormalSubgroup Γ) (hU : proLResOf l H ≤ U.toSubgroup)
      (h : Γ) (hh : h ∈ H) : ∃ e : ℕ, h ^ l ^ e ∈ U.toSubgroup := by
    classical
    have : CompactSpace H := isCompact_iff_compactSpace.mp hHc.isCompact
    let K := U.toSubgroup.comap H.subtype
    have hKo : IsOpen (K : Set H) := U.isOpen.preimage continuous_subtype_val
    have hleK : proLRes l H ≤ K := Subgroup.map_le_iff_le_comap.mp hU
    let ι := {N : OpenNormalSubgroup H // IsPGroup l (H ⧸ N.toSubgroup)}
    let t : ι → Set H := fun i => i.1.toSubgroup
    have hdisjoint : Disjoint (K : Set H)ᶜ (⋂ i, t i) := by
      simp only [Set.disjoint_left, Set.mem_compl_iff, Set.mem_iInter]
      exact fun y hy hall => hy (hleK (mem_proLRes.mpr fun N hN => hall ⟨N, hN⟩))
    obtain ⟨s, hs⟩ := hKo.isClosed_compl.isCompact.elim_finite_subfamily_closed t
      (fun i => i.1.toOpenSubgroup.isClosed) hdisjoint
    let g : H := ⟨h, hh⟩
    have hk (i : ι) : ∃ k : ℕ, g ^ l ^ k ∈ i.1.toSubgroup :=
      (pq_iff l H _).mp i.2 g
    choose k hk using hk
    refine ⟨∑ i ∈ s, k i, ?_⟩
    change g ^ l ^ (∑ i ∈ s, k i) ∈ K
    by_contra hg
    apply Set.disjoint_left.mp hs hg
    simp only [Set.mem_iInter]
    intro i hi
    have hki : k i ≤ ∑ j ∈ s, k j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
    have hpow : l ^ (∑ j ∈ s, k j) = l ^ k i * l ^ (∑ j ∈ s, k j - k i) := by
      rw [← pow_add, Nat.add_sub_cancel' hki]
    change g ^ l ^ (∑ j ∈ s, k j) ∈ i.1.toSubgroup
    rw [hpow, pow_mul]
    exact Subgroup.pow_mem _ (hk i) _
  have heq : PL (l := l) H = proLResOf l H := by
    have := hPn
    apply le_antisymm
    · intro x hx
      by_contra hxP
      have hsI := ProfiniteGrp.closedSubgroup_eq_sInf_open
        (⟨proLResOf l H, hPc⟩ : ClosedSubgroup Γ)
      have h2 : x ∉ ((⟨proLResOf l H, hPc⟩ : ClosedSubgroup Γ) : Subgroup Γ) := hxP
      rw [hsI, Subgroup.mem_sInf] at h2
      push Not at h2
      obtain ⟨K, ⟨hKo, hPK⟩, hxK⟩ := h2
      obtain ⟨U, hPU, hUK⟩ := exists_core K (proLResOf l H) hKo hPK
      exact hxK (hUK (mem_PL.mp hx U (hPcond U hPU)))
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_PL]
      intro U hU
      let N : OpenNormalSubgroup H :=
        { toOpenSubgroup := ⟨U.toSubgroup.comap H.subtype,
            U.toOpenSubgroup.isOpen.preimage continuous_subtype_val⟩
          isNormal' := Subgroup.Normal.comap U.isNormal' _ }
      have : N.toSubgroup.Normal := N.isNormal'
      have hpg : IsPGroup l (H ⧸ N.toSubgroup) :=
        (pq_iff l H _).mpr fun g => hU g g.2
      exact mem_proLRes.mp hy N hpg
  have hiff : ∀ U : OpenNormalSubgroup Γ,
      PL (l := l) H ≤ U.toSubgroup ↔ ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U := by
    exact fun U => ⟨fun h => (hPcond U (heq ▸ h)), cond_le U⟩
  have hbot : PL (l := l) H = ⊥ ↔ IsProL l H := by
    rw [isProL_iff]
    constructor
    · intro hb N g
      let K : Subgroup Γ := N.toSubgroup.map H.subtype
      have hKo : IsOpen (K : Set Γ) := by
        rw [Subgroup.coe_map]
        exact hHo.isOpenMap_subtype_val _ N.toOpenSubgroup.isOpen
      obtain ⟨U, -, hUK⟩ := exists_core K ⊥ hKo bot_le
      obtain ⟨e, he⟩ := (hiff U).mp (by rw [hb]; exact bot_le) g g.2
      refine ⟨e, ?_⟩
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp (hUK he)
      have hy' : y = g ^ l ^ e := Subtype.ext hyg
      rwa [← hy']
    · intro hP
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have key : ∀ W : OpenNormalSubgroup Γ, x ∈ W.toSubgroup := by
        intro W
        apply cond_le W _ hx
        intro h hh
        let N : OpenNormalSubgroup H :=
          { toOpenSubgroup := ⟨W.toSubgroup.comap H.subtype,
              W.toOpenSubgroup.isOpen.preimage continuous_subtype_val⟩
            isNormal' := Subgroup.Normal.comap W.isNormal' _ }
        obtain ⟨k, hk⟩ := hP N ⟨h, hh⟩
        exact ⟨k, hk⟩
      by_contra hne
      obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (isOpen_compl_singleton (x := x)) (by simpa [eq_comm] using hne)
      exact hU (key U) rfl
  exact ⟨hnorm, hclosed, hle, hiff, hbot, heq⟩
