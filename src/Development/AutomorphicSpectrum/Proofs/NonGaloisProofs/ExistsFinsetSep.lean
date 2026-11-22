import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CupFlipContinuousCocycle
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLattices
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasis

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.Kernels

theorem mem_of_forall_pow {O M : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [AddCommGroup M] [Module O M] (Λ E : Submodule O M) (hΛ : Λ.FG) (ϖ : O) (hϖ : ¬ IsUnit ϖ)
    (w : M) (h : ∀ n : ℕ, ∃ e ∈ E, ∃ t ∈ Λ, w = e + ϖ ^ n • t) : w ∈ E := by
  classical
  set N : Submodule O (M ⧸ E) := Λ.map E.mkQ with hNdef
  have hNfg : N.FG := hΛ.map _
  haveI : Module.Finite O N := Module.Finite.iff_fg.2 hNfg
  have hE : ∀ e ∈ E, E.mkQ e = 0 := fun e he => (Submodule.Quotient.mk_eq_zero E).2 he
  obtain ⟨e₀, he₀, t₀, ht₀, hw₀⟩ := h 0
  have hwN : E.mkQ w ∈ N := ⟨t₀, ht₀, by rw [hw₀, pow_zero, one_smul, map_add, hE e₀ he₀, zero_add]⟩
  have hI : Ideal.span {ϖ} ≠ ⊤ := fun h' => hϖ (Ideal.span_singleton_eq_top.1 h')
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (Ideal.span {ϖ}) hI
  have hmem : (⟨E.mkQ w, hwN⟩ : N) ∈ (⨅ i : ℕ, Ideal.span {ϖ} ^ i • ⊤ : Submodule O N) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨e, he, t, ht, hw⟩ := h i
    have htN : E.mkQ t ∈ N := ⟨t, ht, rfl⟩
    have heq : (⟨E.mkQ w, hwN⟩ : N) = ϖ ^ i • (⟨E.mkQ t, htN⟩ : N) := by
      apply Subtype.ext
      rw [Submodule.coe_smul]
      show E.mkQ w = ϖ ^ i • E.mkQ t
      rw [hw, map_add, map_smul, hE e he, zero_add]
    rw [heq]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self ϖ) i) Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  have h0 : E.mkQ w = 0 := congrArg Subtype.val hmem
  exact (Submodule.Quotient.mk_eq_zero E).1 h0

theorem exists_finset_sep {k U G X : Type} [Field k] [AddCommGroup U] [Module k U]
    [FiniteDimensional k U] [AddCommGroup X] [Module k X] (φ : U →ₗ[k] G → X) :
    ∃ F : Finset G, ∀ u, (∀ g ∈ F, φ u g = 0) → φ u = 0 := by
  classical
  let Kf : Finset G → Submodule k U := fun F => ⨅ g ∈ F, LinearMap.ker ((LinearMap.proj g).comp φ)
  obtain ⟨_, ⟨F, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Submodule k U)) (Set.range Kf)
    ⟨Kf ∅, Set.mem_range_self _⟩
  have hall : ∀ g, Kf F ≤ LinearMap.ker ((LinearMap.proj g).comp φ) := by
    intro g
    have hle : Kf (insert g F) ≤ Kf F := by
      refine le_iInf₂ fun g' hg' => iInf₂_le g' (Finset.mem_insert_of_mem hg')
    have heq : Kf (insert g F) = Kf F := by
      by_contra hne
      exact hmin _ (Set.mem_range_self _) (lt_of_le_of_ne hle hne)
    rw [← heq]
    exact iInf₂_le g (Finset.mem_insert_self g F)
  refine ⟨F, fun u hu => funext fun g => ?_⟩
  have huF : u ∈ Kf F := by
    simp only [Kf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    exact hu
  have := hall g huF
  simpa using this

end GlobalTheory.CompanionTheory.LocDual.Kernels
