import Mathlib

namespace UpperTheory.Reformulated.B.Qi13

theorem aux1 :
    ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [IsNonarchimedeanLocalField K], IsLocalRing ↥(ValuativeRel.valuation K).integer := by
  intro K _ _ _ _
  infer_instance

@[reducible] noncomputable def algRes (K : Type) [inst : Field K]
    [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K]
    (l : ℕ) [inst_4 : Fact l.Prime] :
    [@CharP (@IsLocalRing.ResidueField _ _ (aux1 K)) _ l] →
    (letI := aux1 K; Algebra (ZMod l) (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)) :=
  fun [h : _] => @ZMod.algebra _ _ l h

@[reducible] noncomputable def fdim (K : Type) [inst : Field K]
    [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K]
    (l : ℕ) [Fact l.Prime]
    [@CharP (@IsLocalRing.ResidueField _ _ (aux1 K)) _ l] : ℕ :=
  letI := aux1 K
  letI := algRes K l
  Module.finrank (ZMod l) (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)

theorem aux4 :
    ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [inst_3 : IsNonarchimedeanLocalField K] (l : ℕ) [inst_4 : Fact l.Prime]
      [inst_5 : CharP (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) l],
      letI := algRes K l
      Module.Free (ZMod l) (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) := by
  intro K _ _ _ _ l _ _
  letI := algRes K l
  exact Module.Free.of_divisionRing (ZMod l) _

theorem aux5 : ∀ (l : ℕ) [Fact l.Prime], StrongRankCondition (ZMod l) := by
  intro l _
  infer_instance

theorem aux6 :
    ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [inst_3 : IsNonarchimedeanLocalField K] (l : ℕ) [inst_4 : Fact l.Prime]
      [inst_5 : CharP (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) l],
      letI := algRes K l
      Module.Finite (ZMod l) (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) := by
  intro K _ _ _ _ l _ _
  letI := algRes K l
  haveI : Finite (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) := inferInstance
  exact Module.Finite.of_finite

noncomputable def bb (K : Type) [inst : Field K]
    [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K]
    (l : ℕ) [inst_4 : Fact l.Prime]
    [inst_5 : @CharP (@IsLocalRing.ResidueField _ _ (aux1 K)) _ l] :
    letI := aux1 K
    letI := algRes K l
    Module.Basis (Fin (fdim K l)) (ZMod l) (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) :=
  letI := aux1 K
  letI := algRes K l
  letI := aux4 K l
  letI := aux5 l
  letI := aux6 K l
  Module.finBasis (ZMod l) (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)

theorem aux8 :
    ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [inst_3 : IsNonarchimedeanLocalField K] (l : ℕ) [inst_4 : Fact l.Prime]
      [inst_5 : @CharP (@IsLocalRing.ResidueField _ _ (aux1 K)) _ l] (i : Fin (fdim K l)),
      letI := aux1 K
      ∃ x : ↥(ValuativeRel.valuation K).integer,
        IsLocalRing.residue ↥(ValuativeRel.valuation K).integer x = bb K l i := by
  intro K _ _ _ _ l _ _ i
  exact IsLocalRing.residue_surjective _

noncomputable def blift (K : Type) [inst : Field K]
    [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K]
    (l : ℕ) [inst_4 : Fact l.Prime]
    [inst_5 : @CharP (@IsLocalRing.ResidueField _ _ (aux1 K)) _ l] :
    Fin (fdim K l) → ↥(ValuativeRel.valuation K).integer :=
  letI := aux1 K
  fun i =>
    @Exists.choose ↥(ValuativeRel.valuation K).integer
      (fun x => IsLocalRing.residue ↥(ValuativeRel.valuation K).integer x = bb K l i)
      (aux8 K l i)

private theorem key {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K]
    (O : Subring K) {k : Type} [CommRing k] [Algebra (ZMod l) k] (r : O →+* k)
    (hO : ∀ c : ℤ_[l], algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O) {ι : Type} [Fintype ι] (x : ι → O)
    (h : LinearIndependent (ZMod l) (fun i => r (x i))) :
    LinearIndependent ℚ_[l] (fun i => (x i : K)) := by
  classical
  let φ : ℤ_[l] →+* O :=
    ((algebraMap ℚ_[l] K).comp PadicInt.Coe.ringHom).codRestrict O hO
  have hφ : ∀ c : ℤ_[l], r (φ c) = algebraMap (ZMod l) k (PadicInt.toZMod c) := by
    intro c
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (PadicInt.toZMod c)
    have hker : c - (n : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, hn, sub_self]
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hker
    obtain ⟨d, hd⟩ := hker
    have hl : (l : k) = 0 := by
      rw [← map_natCast (algebraMap (ZMod l) k), ZMod.natCast_self, map_zero]
    have hc : c = n + l * d := by rw [← hd]; ring
    rw [← hn, hc]
    simp only [map_add, map_mul, map_natCast, hl, zero_mul, add_zero]
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hne
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => ‖g i‖) ⟨i₀, Finset.mem_univ _⟩
  have hpos : 0 < ‖g m‖ := (norm_pos_iff.mpr hi₀).trans_le (hm i₀ (Finset.mem_univ _))
  have hgm : g m ≠ 0 := norm_pos_iff.mp hpos
  let c : ι → ℤ_[l] := fun i => ⟨g i / g m, by
    rw [norm_div]
    exact (div_le_one hpos).mpr (hm i (Finset.mem_univ _))⟩
  have hsum : ∑ i, φ (c i) * x i = 0 := by
    apply Subtype.ext
    have h1 : ∀ i, ((φ (c i) * x i : O) : K) = (g m)⁻¹ • (g i • (x i : K)) := by
      intro i
      change algebraMap ℚ_[l] K (g i / g m) * (x i : K) = _
      rw [smul_smul, Algebra.smul_def, div_eq_inv_mul]
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [h1]
    rw [← Finset.smul_sum, hg, smul_zero]
    rfl
  have hred : ∑ i, PadicInt.toZMod (c i) • r (x i) = 0 := by
    have h2 := congrArg r hsum
    rw [map_sum, map_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hφ, Algebra.smul_def]
  have h3 := h _ hred m
  have h4 : c m = 1 := Subtype.ext (div_self hgm)
  rw [h4, map_one] at h3
  exact one_ne_zero h3

private theorem mem_of_closed {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [TopologicalSpace K] [Algebra ℚ_[l] K] (O : Subring K) (hO : IsClosed (O : Set K))
    (hc : Continuous (algebraMap ℚ_[l] K)) (c : ℤ_[l]) :
    algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O := by
  refine PadicInt.denseRange_natCast.induction_on
    (p := fun c : ℤ_[l] => algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O) c ?_ ?_
  · exact hO.preimage (hc.comp continuous_subtype_val)
  · intro n
    rw [PadicInt.coe_natCast, map_natCast]
    exact natCast_mem O n

theorem linIndep :
    ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [inst_3 : IsNonarchimedeanLocalField K] (l : ℕ) [inst_4 : Fact l.Prime]
      [inst_5 : Algebra ℚ_[l] K] [inst_6 : CharP (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) l],
      Continuous (algebraMap ℚ_[l] K) →
      LinearIndependent ℚ_[l] (fun i : Fin (fdim K l) => (blift K l i : K)) := by
  intro K _ _ _ _ l _ _ _ hc
  letI := algRes K l
  refine key (ValuativeRel.valuation K).integer
    (IsLocalRing.residue (ValuativeRel.valuation K).integer)
    (mem_of_closed _ Valuation.isClosed_integer hc)
    (blift K l) ?_
  have h : (fun i => IsLocalRing.residue (ValuativeRel.valuation K).integer
      (blift K l i)) = bb K l :=
    funext fun i => (aux8 K l i).choose_spec
  rw [h]
  exact (bb K l).linearIndependent

end UpperTheory.Reformulated.B.Qi13
