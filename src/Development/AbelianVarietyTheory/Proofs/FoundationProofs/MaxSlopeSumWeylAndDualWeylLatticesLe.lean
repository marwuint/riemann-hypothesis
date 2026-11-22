import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeLeLogOfIntegralHermitianForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PairingNormalisingConstantLogLeBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtNormMulWeylPairingIntegralSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDual
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem testLatticeCondition_sumLat_nabK_and_delK : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric (sumGram lam e G) X → TestLatticeCondition N X (sumLat lam e fun c => nabK lam (M c)) (bound (Fintype.card ι) n R) ∧ TestLatticeCondition N X (sumLat lam e fun c => delK lam (M c)) (bound (Fintype.card ι) n R) := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hsp G hG C _ M hM N e X hX
  classical
  obtain ⟨s, hs0, hs, hlog⟩ := _root_.GlobalTheory.extNorm_eq_nat_log_le_bound K ι n lam R hR hsp
  have hlat := fun c => _root_.GlobalTheory.TransLattice.nabDelLattice K ι n lam (M c) (fun τ => (hM c τ).1)
  have main : ∀ T : C → Submodule (𝓞 K) (VV K lam), (∀ c, Submodule.IsLattice K (T c)) →
      (∀ c, T c ≤ nabK lam (M c)) → TestLatticeCondition N X (sumLat lam e T) (bound (Fintype.card ι) n R) := by
    intro T hT hle
    obtain ⟨hL, hN, -⟩ := _root_.GlobalTheory.TestLat.SumLat.sumLat_lattice_dual K ι n lam C N e T hT
    haveI : Finite C :=
      Finite.of_injective (fun c => e.symm (c, (e ⟨0, hN⟩).2)) (fun a b h => by
        simpa using h)
    letI : Fintype C := Fintype.ofFinite C
    obtain ⟨hval, hdef, -, hdet⟩ := _root_.GlobalTheory.TestLat.sumGram_spec K ι n lam G hG C N e
    have hne : sumLat lam e T ≠ ⊥ := by
      intro h
      have h2 := hL.span_eq_top
      rw [h] at h2
      haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
      simp at h2
    refine ⟨hL.fg, hne, fun v => (hX v).1, le_trans ?_ hlog⟩
    refine _root_.GlobalTheory.muMaxDef_le_log_of_integral K v₀ hv N (sumGram lam e G) X ⟨hdef.2.1, hX⟩ s hs0 _ hL.fg hne ?_
    intro x hx y hy
    rw [hval, Finset.mul_sum, ← hs]
    refine Subring.sum_mem _ fun c _ => ?_
    have hmem : ∀ z ∈ sumLat lam e T, valAt lam e c z ∈ nabK lam (M c) := fun z hz =>
      hle c ((Submodule.mem_iInf _).1 hz c)
    exact _root_.GlobalTheory.PairInt.extNorm_mul_pairK_integral K ι n lam G (M c) (fun τ => (hG τ).1) hdet (hM c) _ (hmem x hx) _ (hmem y hy)
  exact ⟨main _ (fun c => (hlat c).1) (fun c => le_rfl),
    main _ (fun c => (hlat c).2) (fun c => delLeNab K ι n lam (M c))⟩

end GlobalTheory.TestLat
