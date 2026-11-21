import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.BlochKatoIntegralScalars

section Local

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_of_norm_le_one (K : Loc.FinExt l) (x : K.1) (h : ‖(x : PadicAlgCl l)‖ ≤ 1) :
    x ∈ Loc.OL K :=
  (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1
    (isIntegral_of_norm_le_one _ h)

theorem compactSpace_GK (K : Loc.FinExt l) : CompactSpace ↥(Loc.GK K) := by
  haveI := K.2
  have h : IsClosed ((Loc.GK K : Subgroup (Loc.GQ l)) : Set (Loc.GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed K.1
  exact isCompact_iff_compactSpace.1 h.isCompact

theorem exists_pow_mul_mem_OL {X : Type} [TopologicalSpace X] [CompactSpace X] (K : Loc.FinExt l) {m : ℕ}
    (c : X → Fin m → K.1) (hc : Continuous c) :
    ∃ N : ℕ, ∀ g j, (l : K.1) ^ N * c g j ∈ Loc.OL K := by
  have hc' : Continuous fun g (j : Fin m) => ((c g j : K.1) : PadicAlgCl l) :=
    continuous_pi fun j => continuous_subtype_val.comp ((continuous_apply j).comp hc)
  obtain ⟨C, hC⟩ := (isCompact_range hc').isBounded.exists_norm_le
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C hl
  refine ⟨N, fun g j => mem_OL_of_norm_le_one K _ ?_⟩
  have h1 : ‖((c g j : K.1) : PadicAlgCl l)‖ ≤ C :=
    (norm_le_pi_norm (fun j : Fin m => ((c g j : K.1) : PadicAlgCl l)) j).trans (hC _ ⟨g, rfl⟩)
  have h2 : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have := PadicAlgCl.norm_extends l (l : ℚ_[l])
    rw [map_natCast] at this
    rw [this, Padic.norm_p]
  have h3 : (((l : K.1) ^ N * c g j : K.1) : PadicAlgCl l) =
      (l : PadicAlgCl l) ^ N * ((c g j : K.1) : PadicAlgCl l) := by
    push_cast
    rfl
  rw [h3, norm_mul, norm_pow, h2, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
  exact h1.trans hN.le

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

end Local

theorem mem_of_mk_mem_span {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (ρ : Representation R G M) (S : Submodule R (G → M)) (hB : ∀ x : M, (fun g => ρ g x - x) ∈ S)
    (A : Set (ReciprocityTheory.Gal.H1 ρ))
    (hA : ∀ x ∈ A, ∃ w : ReciprocityTheory.Gal.Z1 ρ, (w : G → M) ∈ S ∧ x = Submodule.Quotient.mk w)
    (w : ReciprocityTheory.Gal.Z1 ρ) (hw : Submodule.Quotient.mk w ∈ Submodule.span R A) : (w : G → M) ∈ S := by
  have hB' : (ReciprocityTheory.Gal.B1 ρ).comap (ReciprocityTheory.Gal.Z1 ρ).subtype ≤ S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype := by
    intro w hw
    obtain ⟨x, hx⟩ := (mem_coboundaries1 ρ _).1 hw
    have : (ReciprocityTheory.Gal.Z1 ρ).subtype w = fun g => ρ g x - x := funext hx
    rw [Submodule.mem_comap, this]
    exact hB x
  have hle : Submodule.span R A ≤ (S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype).map (Submodule.mkQ _) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hA x hx
    exact ⟨w, hw, rfl⟩
  have h2 : w ∈ ((S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype).map
      (Submodule.mkQ ((ReciprocityTheory.Gal.B1 ρ).comap (ReciprocityTheory.Gal.Z1 ρ).subtype))).comap (Submodule.mkQ _) :=
    hle hw
  rw [Submodule.comap_map_mkQ, sup_eq_right.2 hB'] at h2
  exact h2

end GlobalTheory.BlochKatoIntegralScalars
