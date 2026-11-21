import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeBaseChangeFieldAndComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisSmulEqValuationSubringOverDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteIndexSubgroupAutExtendSepClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageOfMapEqOneOnInfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaConjMemSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaLiftOfPurelyInseparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepClosureFiniteExtPowMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGalois
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResiduePerfectAndChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisRepresentationTateModuleBaseChangeEqOneIff

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem galTate_eq_one_of_embedding {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω']
    (j : Ω →ₐ[K] Ω') (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (l : ℕ) [Fact l.Prime]
    (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω') (h : ∀ x, σ' (j x) = j (σ x)) (h1 : galTate A l σ' = 1) :
    galTate A l σ = 1 := by
  obtain ⟨f, hf, hc⟩ := _root_.GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois K Ω Ω' j A
  refine LinearMap.ext fun t => Tate.ext fun n => hf ?_
  have e := congrArg (fun u => u.lev n) (LinearMap.congr_fun h1 (Tate.map l f t))
  exact (hc σ σ' h (t.lev n)).trans e

theorem finite_image_inertia_of_goodReduction_baseChange (h : NeronOggShafarevichSt) (R K Ω : Type) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω)
    (hV : IsAbove R K V.toSubring) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (l : ℕ) [Fact l.Prime] (hl : (l : ResidueField R) ≠ 0)
    (L W Ω' : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Algebra W L] [IsFractionRing W L] [Field Ω'] [Algebra L Ω'] [IsSepClosure L Ω']
    [Algebra K Ω'] [IsScalarTower K L Ω'] (hW : IsAbove R K (algebraMap W L).range)
    (hg : HasGoodReduction W L ((Over.pullback (spMap (algebraMap K L))).obj A)) :
    (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite := by
  haveI : IsSepClosed Ω' := IsSepClosure.sep_closed L
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  haveI : IsGalois K Ω := inferInstance
  let j : Ω →ₐ[K] Ω' := IsSepClosed.lift
  obtain ⟨V', hV'⟩ := exists_isAbove W L Ω'
  obtain ⟨hp, hm⟩ := _root_.GlobalTheory.AbVarRedRes.residue_perfect_and_char R K L W hW
  obtain ⟨hAL, hc⟩ := _root_.GlobalTheory.Published.AbVarRed.isAbelianScheme_baseChange_field_and_comm K L A hA
  have hT := (h.iff_tateUnramified hV' hAL l (hm l hl)).1 hg
  have hV'' : IsAbove R K (V'.comap (j : Ω →+* Ω')).toSubring := by
    unfold IsAbove at hW hV' ⊢
    rw [← hW, ← hV']
    ext x
    change j (algebraMap K Ω x) ∈ V' ↔ algebraMap L Ω' (algebraMap K L x) ∈ V'
    rw [j.commutes, ← IsScalarTower.algebraMap_apply]
  obtain ⟨H, hH, hext⟩ := _root_.GlobalTheory.SepExt.exists_finiteIndex_extend K L Ω Ω' j
  obtain ⟨g, hgV⟩ := GlobalTheory.T.exists_galois_smul_eq_valuationSubring_over_dvr R K Ω V _ hV hV''
  have key : ∀ σ ∈ inertia K (V'.comap (j : Ω →+* Ω')), σ ∈ H → galTate A l σ = 1 := by
    intro σ hσ hσH
    obtain ⟨σ', hσ'⟩ := hext σ hσH
    have h1 := _root_.GlobalTheory.inertia_lift_of_purelyInseparable K L Ω Ω' j (_root_.GlobalTheory.Published.AbVarRed.sepClosure_finiteExt_pow_mem_range K L Ω Ω' j) V' σ σ' hσ' hσ
    have h2 := (_root_.GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff K L Ω' A l σ').1 (hT σ' h1)
    exact galTate_eq_one_of_embedding j A l σ (σ'.restrictScalars K) hσ' h2
  refine _root_.GlobalTheory.finite_image_of_map_eq_one_on_inf_finiteIndex _ _ (galTate A l) (inertia K V) (H.comap (MulAut.conj g).toMonoidHom) ?_ ?_
  · constructor
    rw [Subgroup.index_comap_of_surjective _ (MulAut.conj g).surjective]
    exact hH.index_ne_zero
  · intro σ hσ hσH
    have h1 := key (g * σ * g⁻¹) (hgV ▸ _root_.GlobalTheory.inertia_conj_mem_smul K Ω V g σ hσ) hσH
    have e : σ = g⁻¹ * (g * σ * g⁻¹) * g := by group
    rw [e, map_mul, map_mul, h1, _root_.mul_one, ← map_mul, inv_mul_cancel, map_one]

theorem finite_image_inertia_of_potentialGoodReduction : NeronOggShafarevichSt → ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → HasPotentialGoodReduction R K A → (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite := by
  intro h R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA l _ hl hP
  obtain ⟨L, W, _, _, _, _, _, _, _, _, hW, hg⟩ := hP
  exact finite_image_inertia_of_goodReduction_baseChange h R K Ω V hV A hA l hl L W (SeparableClosure L) hW hg

end GlobalTheory
