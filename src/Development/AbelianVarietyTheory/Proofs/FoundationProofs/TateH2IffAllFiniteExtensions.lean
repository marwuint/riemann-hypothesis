import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TateLocalDualityTopDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow

noncomputable section

namespace GlobalTheory.TateTopCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo

section Integers

variable {l : ℕ} [Fact l.Prime] {LL O : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
  [CommRing O] [Algebra O LL]

theorem mem_range_of_norm_le (h : GoodO (Qp := ℚ_[l]) LL O) (L' : FinExt l)
    (φ : LL ≃ₐ[ℚ_[l]] ↥L'.1) (x : LL) (hx : ‖((φ x : ↥L'.1) : Om l)‖ ≤ 1) :
    x ∈ Set.range (algebraMap O LL) := by
  obtain ⟨⟨hO, hdvr, hfr⟩, hfd, hmt, htr, hop⟩ := h
  obtain ⟨-, -, hmt', -, -⟩ := (GlobalTheory.LocalIntegers.good_integers l L').1
  have hcont : Continuous φ.symm :=
    IsModuleTopology.continuous_of_linearMap φ.symm.toLinearEquiv.toLinearMap
  have hU : IsOpen (φ.symm ⁻¹' Set.range (algebraMap O LL)) := hop.preimage hcont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 ⟨0, by simp⟩
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt ℚ_[l] hε
  have hc0' : c ≠ 0 := norm_pos_iff.1 hc0
  have hk : ∀ k : ℕ, ∃ b : O, algebraMap O LL b = algebraMap ℚ_[l] LL c * x ^ k := by
    intro k
    have : φ (algebraMap ℚ_[l] LL c * x ^ k) ∈ Metric.ball (0 : ↥L'.1) ε := by
      rw [mem_ball_zero_iff]
      change ‖((φ (algebraMap ℚ_[l] LL c * x ^ k) : ↥L'.1) : Om l)‖ < ε
      rw [map_mul, map_pow, AlgEquiv.commutes]
      push_cast
      rw [norm_mul, norm_pow]
      have h1 : ‖((algebraMap ℚ_[l] ↥L'.1 c : ↥L'.1) : Om l)‖ = ‖c‖ := PadicAlgCl.norm_extends l c
      calc _ ≤ ‖c‖ * 1 := by
            gcongr
            · exact h1.le
            · exact pow_le_one₀ (norm_nonneg _) hx
        _ < ε := by simpa using hc
    simpa using hball this
  rcases ValuationRing.isInteger_or_isInteger O x with h | ⟨y, hy⟩
  · exact h
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  by_cases hu : IsUnit y
  · obtain ⟨z, hz⟩ := hu.exists_right_inv
    refine ⟨z, ?_⟩
    have := congrArg (algebraMap O LL) hz
    rw [map_mul, hy, map_one] at this
    field_simp at this
    exact this
  · exfalso
    obtain ⟨a, ha⟩ := hk 0
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hc0' (by simpa using ha.symm)
    obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hu ha0
    obtain ⟨b, hb⟩ := hk (n + 1)
    refine hn ⟨b, IsFractionRing.injective O LL ?_⟩
    rw [map_mul, map_pow, hy, hb, ha, inv_pow]
    field_simp

theorem mem_range_iff (h : GoodO (Qp := ℚ_[l]) LL O) (L' : FinExt l)
    (φ : LL ≃ₐ[ℚ_[l]] ↥L'.1) (x : LL) :
    x ∈ Set.range (algebraMap O LL) ↔ φ x ∈ OL L' := by
  have hO : φ x ∈ OL L' ↔ ‖((φ x : ↥L'.1) : Om l)‖ ≤ 1 := mem_integralClosure_padicInt_iff L'.1 _
  rw [hO]
  refine ⟨?_, mem_range_of_norm_le h L' φ x⟩
  rintro ⟨a, rfl⟩
  by_contra hlt
  rw [not_le] at hlt
  have hsurj : Function.Surjective (algebraMap O LL) := by
    intro w
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖((φ w : ↥L'.1) : Om l)‖ hlt
    have hpos : 0 < ‖((φ (algebraMap O LL a) : ↥L'.1) : Om l)‖ ^ k := by positivity
    have ha : algebraMap O LL a ≠ 0 := by
      intro h0
      rw [h0] at hlt
      norm_num at hlt
    obtain ⟨b, hb⟩ := mem_range_of_norm_le h L' φ (w / algebraMap O LL a ^ k) (by
      rw [map_div₀, map_pow]
      push_cast
      rw [norm_div, norm_pow, div_le_one hpos]
      exact hk.le)
    exact ⟨b * a ^ k, by rw [map_mul, map_pow, hb]; field_simp⟩
  obtain ⟨⟨hO, hdvr, hfr⟩, -⟩ := h
  exact IsDiscreteValuationRing.not_isField O
    ((RingEquiv.ofBijective (algebraMap O LL)
      ⟨IsFractionRing.injective O LL, hsurj⟩).toMulEquiv.isField (Field.toIsField LL))

theorem exists_finExt (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] :
    ∃ L' : FinExt l, Nonempty (LL ≃ₐ[ℚ_[l]] ↥L'.1) := by
  let ψ : LL →ₐ[ℚ_[l]] Om l := IsAlgClosed.lift
  exact ⟨⟨ψ.fieldRange, (AlgEquiv.ofInjectiveField ψ).toLinearEquiv.finiteDimensional⟩,
    ⟨AlgEquiv.ofInjectiveField ψ⟩⟩

end Integers

section Quotients

variable {G LL O LL' O' M' : Type} [Group G] [TopologicalSpace G] [Field LL] [CommRing O]
  [Algebra O LL] [Field LL'] [CommRing O'] [Algebra O' LL'] [AddCommGroup M'] [Module O' M']
  [TopologicalSpace M'] [DiscreteTopology M'] [IsTopologicalAddGroup M']
  [ContinuousConstSMul O' M']

omit [TopologicalSpace G] in

def rangeLattice (hinj : Function.Injective (algebraMap O LL)) (χ : G →* LLˣ)
    (hχ : ∀ g, ((χ g : LLˣ) : LL) ∈ Set.range (algebraMap O LL)) :
    Lattice (O := O) (charRep χ) where
  T := LinearMap.range (Algebra.linearMap O LL)
  stable := by
    rintro g x ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := hχ g
    exact ⟨a * y, by simp [charRep, ha]⟩
  fg := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
  span := by
    rw [eq_top_iff]
    intro x _
    have : (1 : LL) ∈ Submodule.span LL ((LinearMap.range (Algebra.linearMap O LL) :
        Submodule O LL) : Set LL) := Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x this

end Quotients

section Compare

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)

def Clause (LL O : Type) [Field LL] [Algebra ℚ_[l] LL] [CommRing O] [Algebra O LL] : Prop :=
  ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
      Nonempty (ReciprocityTheory.Def.H2 (repD L1) ⊤ ≃ₗ[O] (LL ⧸ L1.T))

theorem tate_h2_iff_clause : LocalTateTopDegree (P.PD K) ↔
    ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
      [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → Clause P K LL O := Iff.rfl

end Compare

end GlobalTheory.TateTopCompare
