import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse
import Formalism.PadicSubsetSums.StableGradedCounts.DividedPowerCoeffValuation

noncomputable section

namespace Formalism.MainNotions.ElementDenominator

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section PartII

variable {l : ℕ} [Fact l.Prime]
    {K₀' K' B BdR : Type} [Field K₀'] [Field K'] [Algebra ℚ_[l] K₀'] [Algebra ℚ_[l] K']
    [Algebra K₀' K'] [IsScalarTower ℚ_[l] K₀' K'] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B]
    [Algebra ↥(K0 (qlExt l)) B] [IsScalarTower ℚ_[l] ↥(K0 (qlExt l)) B] [Algebra K₀' B]
    [IsScalarTower ℚ_[l] K₀' B] [Algebra ℚ_[l] BdR] [Algebra ↥(K0 (qlExt l)) BdR]
    [Algebra ↥(qlExt l).1 BdR] [IsScalarTower ℚ_[l] ↥(qlExt l).1 BdR]
    [IsScalarTower ↥(K0 (qlExt l)) ↥(qlExt l).1 BdR] [IsScalarTower ℚ_[l] ↥(K0 (qlExt l)) BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower ℚ_[l] K' BdR] [IsScalarTower K₀' K' BdR]
    [IsScalarTower ℚ_[l] K₀' BdR]
    (PC : PotCrysData ↥(GK (qlExt l)) ℚ_[l] ↥(K0 (qlExt l)) ↥(qlExt l).1 K₀' K' B BdR)
    (LL : FinExt l)

def HypT (T₁ T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (N η H : ℕ)
    (U : Finset ℤ) (Sig : Finset (PC.Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l))) : Prop :=
  PC.IsPotCrys T₁.ρ ∧ PC.IsPotCrys T₂.ρ ∧ F.Onto ∧
    PC.IsFrob Fr ∧ FrobStable PC.Iner Fr Sig ∧ 1 ∈ Sig ∧ Sig.card ≤ N ∧ 2 ≤ N ∧
    PC.InertiaThrough T₁.ρ Sig ∧ PC.InertiaThrough T₂.ρ Sig ∧
    (∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) ∧ (0 : ℤ) ∈ U ∧ U.card ≤ N + 1 ∧ 1 ≤ η ∧ η < H ∧
    (∀ τ, JumpsInV PC.PD T₁.ρ τ (U : Set ℤ)) ∧ (∀ τ, JumpsInV PC.PD T₂.ρ τ (U : Set ℤ))

variable {PC LL}

variable (PC LL)

end PartII

def TwoStep {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (l g g₀ e e' : ℕ)
    (Z Bc I : Submodule O M) : Prop :=
  ∃ s s₀ : Finset M, s.card ≤ g ∧ Submodule.span O (s : Set M) ⊔ Bc = Z ∧
    s₀.card ≤ g₀ ∧ (s₀ : Set M) ⊆ Z ∧
    (∀ p ∈ Z, (l ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) ∧
    (∀ p ∈ Submodule.span O (s₀ : Set M), (l ^ e' : ℕ) • p ∈ I)

theorem len_ne_top {O : Type} [CommRing O] [IsDedekindDomain O] (x : O) (h : x ≠ 0) :
    Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤ := by
  rw [Module.length_ne_top_iff]
  apply isFiniteLength_quotient_span_singleton
  rwa [mem_nonZeroDivisors_iff_ne_zero]

theorem len_le_nat {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (l p g g₀ y e' k : ℕ)
    (Z Bc I : Submodule O M) (h : TwoStep l g g₀ y e' Z Bc I) (hB : Bc ≤ I) (hp : p = l)
    (hk : Module.length O (O ⧸ Ideal.span {((p : ℕ) : O)}) = (k : ℕ∞)) :
    ∃ m : ℕ, Module.length O (↥Z ⧸ I.comap Z.subtype) = (m : ℕ∞) ∧ m ≤ (g * y + g₀ * e') * k := by
  subst hp
  obtain ⟨s, s₀, hs, hgen, hs₀, hsub, h1, h2⟩ := h
  have key := Formalism.IrreducibleCountingLemmas.WindowSums.colength_bound_two_layers O M p g g₀ y e' Z Bc I s s₀ hs hgen hB hs₀ hsub h1 h2
  rw [hk] at key
  have hcol : Module.length O (↥Z ⧸ I.comap Z.subtype) ≤ (((g * y + g₀ * e') * k : ℕ) : ℕ∞) := by
    push_cast
    exact key
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hcol)
  refine ⟨m, hm.symm, ?_⟩
  rw [← hm] at hcol
  exact_mod_cast hcol

section PartI

variable {l : ℕ} [Fact l.Prime]

theorem lenOl_finite (P : LocPrime l) (K LL : FinExt l) :
    ∃ k : ℕ, lenOl (P.PD K) (O := ↥(OL LL)) = (k : ℕ∞) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsDedekindDomain ↥(OL LL) := integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1
  have hne : lenOl (P.PD K) (O := ↥(OL LL)) ≠ ⊤ := by
    apply len_ne_top
    rw [P.PD_p K]
    intro h
    have h2 := congrArg (Subtype.val : ↥(OL LL) → ↥LL.1) h
    have h3 : ((l : ℕ) : ↥LL.1) = 0 := by simpa using h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h3)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
  exact ⟨k, hk.symm⟩

theorem colLe_mono (P : LocPrime l) (K LL : FinExt l) {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)}
    (F : LatHom T₁.L T₂.L) {b b' : ℝ} (hb : b ≤ b') (h : colLe P K LL F b) : colLe P K LL F b' := by
  obtain ⟨m, k, h1, h2, h3⟩ := h
  exact ⟨m, k, h1, h2, h3.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg k))⟩

theorem colLe_of_twoStep (P : LocPrime l) (K LL : FinExt l)
    {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (F : LatHom T₁.L T₂.L) (g g₀ y e' : ℕ)
    (h : TwoStep l g g₀ y e' (latticeFiniteCocycles (P.PD K) T₂.L) (latticeCoboundaries T₂.L) (F.ImF (P.PD K))) :
    colLe P K LL F ((g : ℝ) * y + (g₀ : ℝ) * e') := by
  obtain ⟨k, hk⟩ := lenOl_finite P K LL
  obtain ⟨m, hm, hmk⟩ := len_le_nat l (P.PD K).p g g₀ y e' k _ _ _ h le_sup_right (P.PD_p K) hk
  refine ⟨m, k, hm, hk, ?_⟩
  exact_mod_cast hmk

def HypA (P : LocPrime l) (K LL : FinExt l) (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (F : LatHom T₁.L T₂.L) (r S η m h : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
    (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) : Prop :=
  IsCrys (P.PD K) T₁.ρ ∧ IsCrys (P.PD K) T₂.ρ ∧ F.Onto ∧
    finrank ↥LL.1 T₂.V = r ∧
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, η < b τ) ∧
    (∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) T₂.ρ τ a ≤ m) ∧
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) ∧
    (finrank ↥(K0 K) ↥K.1 = 2 ∨ ∀ τ τ', intersection_update_fsHerm_neg_one K τ = intersection_update_fsHerm_neg_one K τ' → up τ = up τ')

end PartI

end Formalism.MainNotions.ElementDenominator

end
