import Mathlib

namespace UpperTheory.Reformulated.B.CovariantDegrees

noncomputable def jE :
    {l : ℕ} → [hl : Fact l.Prime] → {E Ω : Type} → [inst : Field E] →
    [inst_1 : Field Ω] → [Algebra E Ω] → (Ω →+* PadicAlgCl l) → E →+* PadicAlgCl l :=
  fun {_} [_] {E} {_} [_] [_] [_] j => j.comp (algebraMap E _)

theorem aux2 : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E], Module.Free ℚ E := by
  intros
  infer_instance

noncomputable def KwF :
    {l : ℕ} → [hl : Fact l.Prime] → {E Ω : Type} → [inst : Field E] →
    [NumberField E] → [inst_2 : Field Ω] → [Algebra E Ω] →
    (Ω →+* PadicAlgCl l) → IntermediateField ℚ_[l] (PadicAlgCl l) :=
  fun {l} [_] {E} {_} [_] [_] [_] [_] j =>
    letI := aux2 (E := E)
    IntermediateField.adjoin ℚ_[l] (Set.range fun i : Fin (Module.finrank ℚ E) =>
      jE j (Module.finBasis ℚ E i))

@[reducible] noncomputable def G.{u_1, u_2} (F : Type u_1) (Ω : Type u_2)
    [inst : Field F] [inst_1 : Field Ω] [Algebra F Ω] : Type u_2 :=
  Ω ≃ₐ[F] Ω

noncomputable def Dec.{u_1, u_2} :
    {F : Type u_1} → {Ω : Type u_2} → [inst : Field F] → [inst_1 : Field Ω] →
    [inst_2 : Algebra F Ω] → ValuationSubring Ω → Subgroup (G F Ω) :=
  fun {F Ω} [_] [_] [_] A => A.decompositionSubgroup F

theorem aux6 : ∀ {E Ω : Type} [inst : Field E] [inst_1 : Field Ω]
    [inst_2 : Algebra E Ω], Module.IsTorsionFree E Ω := by
  intros
  infer_instance

theorem aux7 : ∀ {Ω : Type} [inst : Field Ω] [inst_1 : CharZero Ω], Module.IsTorsionFree ℚ Ω := by
  intros
  infer_instance

@[reducible] noncomputable def Om (l : ℕ) [Fact l.Prime] : Type :=
  PadicAlgCl l

@[reducible] noncomputable def GQ (l : ℕ) [Fact l.Prime] : Type :=
  Gal(Om l/ℚ_[l])

theorem laurent_T_neg_one_mul_T_one :
    ∀ {l : ℕ} [hl : Fact l.Prime], IsScalarTower ℚ ℚ_[l] (Om l) := by
  intros
  infer_instance

theorem aux11 :
    ∀ {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [inst : Field Ω] [inst_1 : CharZero Ω]
      (j : Ω →+* PadicAlgCl l),
      letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
      IsScalarTower ℚ Ω (PadicAlgCl l) := by
  intro l hl Ω _ _ j
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem aux12 :
    ∀ {Ω : Type} [inst : Field Ω] [inst_1 : CharZero Ω] [IsAlgClosure ℚ Ω], Normal ℚ Ω := by
  intros
  infer_instance

noncomputable def resQ :
    {l : ℕ} → [hl : Fact l.Prime] → {Ω : Type} → [inst : Field Ω] →
    [inst_1 : CharZero Ω] → [@IsAlgClosure ℚ Ω _ _ _ (aux7 (Ω := Ω))] →
    (Ω →+* PadicAlgCl l) → GQ l → Ω ≃ₐ[ℚ] Ω :=
  fun {l} [_] {Ω} [_] [_] [_] j σ =>
    letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
    letI := aux11 j
    letI : Normal ℚ Ω := aux12
    letI := laurent_T_neg_one_mul_T_one (l := l)
    (σ.restrictScalars ℚ).toAlgHom.restrictNormal' Ω

private theorem j_resQ {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l) (σ : GQ l) (x : Ω) :
    j (resQ j σ x) = σ (j x) := by
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI := aux11 j
  haveI : Normal ℚ Ω := aux12
  exact AlgHom.restrictNormal_commutes (σ.restrictScalars ℚ).toAlgHom Ω x

private theorem jE_mem {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (j : Ω →+* PadicAlgCl l) (x : E) :
    jE j x ∈ KwF (E := E) j := by
  rw [← (Module.finBasis ℚ E).sum_repr x, map_sum]
  refine sum_mem fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

theorem zero_contDiffOn_supported :
    ∀ {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [inst : Field E] [inst_1 : NumberField E]
      [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [inst_4 : CharZero Ω] [inst_5 : IsAlgClosure ℚ Ω]
      (j : Ω →+* PadicAlgCl l) (σ : GQ l),
      σ ∈ (KwF (E := E) j).fixingSubgroup → ∀ x : E, resQ j σ (algebraMap E Ω x) = algebraMap E Ω x := by
  intro l hl E Ω _ _ _ _ _ _ j σ hσ x
  apply j.injective
  refine (j_resQ j σ _).trans ?_
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (jE_mem j x)

noncomputable def resE {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [inst : Field E]
    [inst_1 : NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
    [inst_4 : CharZero Ω] [@IsAlgClosure ℚ Ω _ _ _ (aux7 (Ω := Ω))]
    (j : Ω →+* PadicAlgCl l) (σ : GQ l) :
    σ ∈ (KwF (E := E) j).fixingSubgroup → G E Ω :=
  fun hσ =>
    AlgEquiv.ofRingEquiv (f := (resQ j σ).toRingEquiv) (zero_contDiffOn_supported j σ hσ)

private theorem j_resE {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l)
    (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) (x : Ω) :
    j (resE j σ hσ x) = σ (j x) :=
  j_resQ j σ x

open Pointwise in
private theorem resE_mem {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l}
    {A : ValuationSubring Ω} (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1)
    (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) :
    resE j σ hσ ∈ Dec A := by
  have hn : ∀ x, ‖j (resE j σ hσ x)‖ = ‖j x‖ := fun x => by
    rw [j_resE]
    exact (spectralNorm_eq_of_equiv σ (j x)).symm
  refine MulAction.mem_stabilizer_iff.2 (SetLike.ext fun x => ?_)
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hj, hj, ← hn]
  simp

theorem column_matrix_mul_inverse :
    ∀ {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [inst : Field E] [inst_1 : NumberField E]
      [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
      {j : Ω →+* PadicAlgCl l} (σ : (KwF (E := E) j).fixingSubgroup),
      (σ : GQ l) ∈ (KwF (E := E) j).fixingSubgroup := by
  intro l hl E Ω _ _ _ _ j σ
  exact σ.2

theorem complex_normed_instance_compat :
    ∀ {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [inst : Field E] [inst_1 : NumberField E]
      [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
      [IsAlgClosure E Ω] [inst_5 : CharZero Ω] [inst_6 : IsAlgClosure ℚ Ω]
      {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω},
      (∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) → ∀ σ : (KwF (E := E) j).fixingSubgroup,
      resE j σ.1 (column_matrix_mul_inverse σ) ∈ Dec (F := E) A := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj σ
  exact resE_mem hj _ _

theorem padic_embedding_algebra_compat :
    ∀ {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [inst : Field E] [inst_1 : NumberField E]
      [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
      {j : Ω →+* PadicAlgCl l},
      ((1 : (KwF (E := E) j).fixingSubgroup) : GQ l) ∈ (KwF (E := E) j).fixingSubgroup := by
  intro l hl E Ω _ _ _ _ j
  exact Subgroup.one_mem _

theorem blockM_one_partner_eq_one :
    ∀ {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [inst : Field E] [inst_1 : NumberField E]
      [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
      [IsAlgClosure E Ω] [inst_5 : CharZero Ω] [inst_6 : IsAlgClosure ℚ Ω]
      {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω},
      (∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) →
      resE j ((1 : (KwF (E := E) j).fixingSubgroup) : GQ l) padic_embedding_algebra_compat ∈ Dec (F := E) A := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj
  exact resE_mem hj _ _

theorem blockM_mul_alt :
    ∀ {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [inst : Field E] [inst_1 : NumberField E]
      [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
      [inst_4 : IsAlgClosure E Ω] [inst_5 : CharZero Ω] [inst_6 : IsAlgClosure ℚ Ω]
      {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω} (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1),
      (⟨resE j ((1 : (KwF (E := E) j).fixingSubgroup) : GQ l) padic_embedding_algebra_compat,
        blockM_one_partner_eq_one hj⟩ : Dec (F := E) A) = 1 := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj
  refine Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)
  exact j_resE (E := E) j 1 (Subgroup.one_mem _) x

theorem conj_invariant_character_mem :
    ∀ {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [inst : Field E] [inst_1 : NumberField E]
      [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
      {j : Ω →+* PadicAlgCl l} (σ τ : (KwF (E := E) j).fixingSubgroup),
      ((σ * τ : (KwF (E := E) j).fixingSubgroup) : GQ l) ∈ (KwF (E := E) j).fixingSubgroup := by
  intro l hl E Ω _ _ _ _ j σ τ
  exact (σ * τ).2

theorem rootGL_mem_unitary :
    ∀ {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [inst : Field E] [inst_1 : NumberField E]
      [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
      [IsAlgClosure E Ω] [inst_5 : CharZero Ω] [inst_6 : IsAlgClosure ℚ Ω]
      {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω},
      (∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) → ∀ σ τ : (KwF (E := E) j).fixingSubgroup,
      resE j (σ * τ).1 (conj_invariant_character_mem σ τ) ∈ Dec (F := E) A := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj σ τ
  exact resE_mem hj _ _

theorem conj_invariant_character_transport :
    ∀ {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [inst : Field E] [inst_1 : NumberField E]
      [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
      [inst_4 : IsAlgClosure E Ω] [inst_5 : CharZero Ω] [inst_6 : IsAlgClosure ℚ Ω]
      {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω}
      (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) (σ τ : (KwF (E := E) j).fixingSubgroup),
      (⟨resE j (σ * τ).1 (conj_invariant_character_mem σ τ),
        rootGL_mem_unitary hj σ τ⟩ : Dec (F := E) A) =
        ⟨resE j σ.1 (column_matrix_mul_inverse σ), complex_normed_instance_compat hj σ⟩ *
        ⟨resE j τ.1 (column_matrix_mul_inverse τ), complex_normed_instance_compat hj τ⟩ := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj σ τ
  refine Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)
  refine (j_resE j (σ * τ).1 (σ * τ).2 x).trans ?_
  refine Eq.symm ((j_resE j σ.1 σ.2 (resE j τ.1 τ.2 x)).trans ?_)
  rw [j_resE]
  rfl

noncomputable def rHom {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [inst : Field E]
    [inst_1 : NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
    [@IsAlgClosure E Ω _ _ _ (aux6 (E := E) (Ω := Ω))]
    [inst_5 : CharZero Ω] [@IsAlgClosure ℚ Ω _ _ _ (aux7 (Ω := Ω))]
    {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω} :
    (∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) →
    (KwF (E := E) j).fixingSubgroup →* Dec (F := E) A :=
  fun hj =>
    { toFun := fun σ => ⟨resE j σ.1 (column_matrix_mul_inverse σ), complex_normed_instance_compat hj σ⟩
      map_one' := blockM_mul_alt hj
      map_mul' := conj_invariant_character_transport hj }

theorem continuous_rHom :
    ∀ {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [inst : Field E] [inst_1 : NumberField E]
      [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
      [inst_4 : IsAlgClosure E Ω] [inst_5 : CharZero Ω] [inst_6 : IsAlgClosure ℚ Ω]
      {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω} (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1),
      Continuous (rHom (E := E) hj) := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj
  have h : Continuous ((Dec A).subtype.comp (rHom (E := E) hj)) := by
    apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one]
    intro s hs
    obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).1 hs
    let b := Module.finBasis E L
    have hU : ∀ᶠ σ : (KwF (E := E) j).fixingSubgroup in nhds 1,
        ∀ i, σ.1 (j (b i)) = j (b i) := by
      refine Filter.eventually_all.2 fun i => ?_
      have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) (j (b i))).preimage
        (continuous_subtype_val (p := fun σ => σ ∈ (KwF (E := E) j).fixingSubgroup))
      exact ho.mem_nhds (Subgroup.one_mem (MulAction.stabilizer _ _))
    refine hU.mono fun σ hσ => hLs ?_
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have key : (resE j σ.1 σ.2).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
      b.ext fun i => j.injective ((j_resE j σ.1 σ.2 (b i)).trans (hσ i))
    exact LinearMap.congr_fun key ⟨x, hx⟩
  exact continuous_induced_rng.2 h

end UpperTheory.Reformulated.B.CovariantDegrees
