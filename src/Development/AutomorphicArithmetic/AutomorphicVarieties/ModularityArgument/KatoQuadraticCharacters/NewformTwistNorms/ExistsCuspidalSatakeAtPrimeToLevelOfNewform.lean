import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.RecMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExPlaceIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.PstRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.WdRelRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.EmbPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NewformAutAtL

open Polynomial

private theorem ss_of_tw' {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep (tw r χ)) : IsSSRep r := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).2 hW)
  exact ⟨W', (key W').1 hW', hc⟩

private theorem ev_not_mem' (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw

private theorem normV_eq' (w : HeightOneSpectrum (𝓞 ℚ)) : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

private theorem normV_rat' {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  have hd : Ideal.absNorm w.asIdeal ∣ p :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [normV_eq']
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact w.isPrime.ne_top

private theorem scale_charpoly' {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod) :
    M.charpoly.map φ = (B.map fun b => X - C b).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim] at h1
    have h2 := natDegree_multiset_prod_X_sub_C_eq_card (B.map (φ c * ·))
    rw [Multiset.map_map] at h2
    simp only [Function.comp_def, Multiset.card_map] at h2
    rw [h2] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hc')
    linear_combination e0
  have ht : φ M.trace = x + y := by
    apply mul_left_cancel₀ hc'
    linear_combination e0 - e1
  rw [hd, ht, C_add, C_mul]
  ring

end GlobalTheory.NewformAutAtL

end

