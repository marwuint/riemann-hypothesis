import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastPowNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsComplOfSaturated

noncomputable section

namespace GlobalTheory.TopSteps.FinSummand

open Module TensorProduct
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

theorem exists_isCompl_of_saturated {O M : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (N : Submodule O M)
    (h : ∀ (a : O) (x : M), a ≠ 0 → a • x ∈ N → x ∈ N) : ∃ C : Submodule O M, IsCompl N C := by
  first
  | exact @_root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated
  | exact _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated
  | (apply _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated ..)

section General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL]

section Rep

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  {ρ : Representation LL G V}

variable [Module O V] [IsScalarTower O LL V] [IsDomain O] [IsFractionRing O LL]

omit [TopologicalSpace G] in

theorem invariants_stableLattice_mod_irreducible_eq_bot [IsDiscreteValuationRing O] (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam)
    (h : (coefRep (latRep L) (O ⧸ Ideal.span {lam})).invariants = ⊥) : H0V ρ = ⊥ := by
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  have hsm : ∀ (a : O) (x : V), a ≠ 0 → a • x = 0 → x = 0 := fun a x ha hx => by
    rw [← algebraMap_smul LL] at hx
    exact (smul_eq_zero.1 hx).resolve_left (by simpa using ha)
  have hM : (latRep L).invariants = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {lam}) _ (IsNoetherian.noetherian _) ?_ ?_
    · intro x hx
      have h1 : x ⊗ₜ[O] (1 : O ⧸ Ideal.span {lam}) ∈
          (coefRep (latRep L) (O ⧸ Ideal.span {lam})).invariants := fun g => by
        rw [coefRep_tmul, hx g]
      rw [h, Submodule.mem_bot] at h1
      have h2 := congrArg (TensorProduct.tensorQuotEquivQuotSMul ↥L.T (Ideal.span {lam})) h1
      rw [map_zero, ← map_one (Ideal.Quotient.mk _), TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul] at h2
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x lam ⊤).1 h2
      refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) fun g => Subtype.ext ?_
      have h3 := congrArg Subtype.val (hx g)
      rw [map_smul] at h3
      refine sub_eq_zero.1 (hsm lam _ hlam.ne_zero ?_)
      rw [smul_sub]
      exact sub_eq_zero.2 h3
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hlam.maximalIdeal_eq]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, ha, hax⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L x
  have h1 : (⟨a • x, hax⟩ : ↥L.T) ∈ (latRep L).invariants := fun g => Subtype.ext (by
    have := (Submodule.mem_iInf _).1 hx g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    change ρ g (a • x) = a • x
    rw [← algebraMap_smul LL, map_smul, this])
  rw [hM, Submodule.mem_bot] at h1
  exact hsm a x ha (congrArg Subtype.val h1)

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem h1fT_saturated (L : Lattice (O := O) ρ) (a : O) (x : LatticeCohomology L) (ha : a ≠ 0) (hx : a • x ∈ latticeFiniteCohomology PD L) :
    x ∈ latticeFiniteCohomology PD L := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨c', hc', h⟩ := hx
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨b, -, hb⟩ := h
  have h1 : ((c' - a • c : ↥(latticeCocycles L)) : G → V) ∈ finiteCocycles PD ρ := by
    refine ⟨(c' - a • c).2.1, b ⊗ₜ 1, fun g => ?_⟩
    have : ρ g b - b = ((c' - a • c : ↥(latticeCocycles L)) : G → V) g := congrFun hb g
    rw [← this]
    simp [actVB, sub_tmul]
  have h2 : algebraMap O LL a • (c : G → V) ∈ finiteCocycles PD ρ := by
    have := (finiteCocycles PD ρ).sub_mem hc'.2 h1
    rw [algebraMap_smul]
    simpa using this
  have ha' : algebraMap O LL a ≠ 0 := by simpa using ha
  have h3 : (c : G → V) ∈ finiteCocycles PD ρ := (Submodule.smul_mem_iff (finiteCocycles PD ρ) ha').1 h2
  exact ⟨c, ⟨c.2, h3⟩, rfl⟩

theorem finrank_h1fT [CompactSpace G] (L : Lattice (O := O) ρ) (hT : IsOpen (L.T : Set V)) :
    finrank O ↥(latticeFiniteCohomology PD L) = finrank LL (FiniteCohomology PD ρ) := by
  refine congrArg Cardinal.toNat (GlobalTheory.BlochKatoRank.rank_subquotient_eq (K := LL) LinearMap.id (latticeCocycles L) (latticeCoboundaries L)
    (latticeFiniteCocycles PD L) (finiteCocycles PD ρ) (B1 ρ) (fun a ha => ha.2) ?_ ?_ ?_)
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · rintro a ⟨x, hx⟩
    obtain ⟨m, hm, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L x
    refine ⟨m, hm, m • x, h, ?_⟩
    rw [map_smul]
    exact congrArg (m • ·) hx
  · intro c hc
    obtain ⟨a, ha, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_fun_mem L hT c hc.1.1
    have h1 : a • c ∈ (finiteCocycles PD ρ).restrictScalars O :=
      Submodule.smul_mem ((finiteCocycles PD ρ).restrictScalars O) a hc
    exact ⟨a, ha, a • c, ⟨h1.1, fun g _ => h g⟩, ⟨⟨h1.1, fun g _ => h g⟩, h1⟩, rfl⟩

end Rep

end General

end GlobalTheory.TopSteps.FinSummand
