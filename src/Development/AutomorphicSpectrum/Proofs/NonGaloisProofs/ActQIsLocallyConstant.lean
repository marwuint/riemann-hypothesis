import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasis

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.FinCoc

section Generic

variable {G LL O V : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V]
  [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}

theorem actQ_one' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (m : ↥L.T ⧸ I) :
    actQ L I hI 1 m = m := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L 1 t) = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext (by simp [actT])

theorem actQ_mul' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (g h : G)
    (m : ↥L.T ⧸ I) : actQ L I hI (g * h) m = actQ L I hI g (actQ L I hI h m) := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L (g * h) t) = Submodule.Quotient.mk (actT L g (actT L h t))
  congr 1
  refine Subtype.ext ?_
  change ρ (g * h) (t : V) = ρ g (ρ h (t : V))
  simp

theorem pow_nsmul_quot (L : Lattice (O := O) ρ) {ϖ : O} {n : ℕ} (hn : (n : O) ∈ Ideal.span {ϖ}) (r : ℕ)
    (m : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) : n ^ r • m = 0 := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hn
  rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hc : ((n ^ r : ℕ) : O) = ϖ ^ r * u ^ r := by
    rw [Nat.cast_pow, ← hu, mul_pow, mul_comm]
  rw [hc, mul_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

variable [TopologicalSpace V] [ContinuousAdd V]

theorem mk_isLocallyConstant (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ}
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V)) :
    IsLocallyConstant (fun x : ↥L.T =>
      (Submodule.Quotient.mk x : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : ↥L.T => (y : V) + -(x : V) :=
    continuous_subtype_val.add continuous_const
  have hev := hc.continuousAt.eventually_mem (x := x)
    (s := (fun x => ϖ ^ r • x) '' (L.T : Set V)) (by simpa using hW)
  filter_upwards [hev] with y hy
  obtain ⟨t, ht, h⟩ := hy
  rw [Submodule.Quotient.eq]
  have hxy : y - x = ϖ ^ r • (⟨t, ht⟩ : ↥L.T) :=
    Subtype.ext (by simpa [sub_eq_add_neg] using h.symm)
  rw [hxy]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem finite_quot (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ} (hC : IsCompact (L.T : Set V))
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V)) :
    Finite (↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) := by
  have hcs : CompactSpace ↥L.T := isCompact_iff_compactSpace.1 hC
  refine Set.finite_univ_iff.1 ?_
  rw [← (Submodule.Quotient.mk_surjective _).range_eq]
  exact (mk_isLocallyConstant L hW).range_finite

theorem actQ_isLocallyConstant [TopologicalSpace G] (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ}
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V))
    (hcont : ∀ x, Continuous fun g => ρ g x)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (m : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) :
    IsLocallyConstant fun g => actQ L _ hI g m := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have hc : Continuous fun g : G => actT L g t := (hcont (t : V)).subtype_mk _
  exact (mk_isLocallyConstant L hW).comp_continuous hc

end Generic

end GlobalTheory.CompanionTheory.FinCoc
