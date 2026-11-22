import Mathlib
import GroundTheory.PAdicHodge.UntiltPerfectoid
import GroundTheory.PAdicHodge.UntiltApprox
import GroundTheory.PAdicHodge.UntiltGalois
import GroundTheory.PAdicHodge.UntiltGaloisCorr
import GroundTheory.PAdicHodge.CompletedAlgClosure

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

theorem exists_isGalois_le {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed L]
    [PerfectField F] (N : IntermediateField F L) [FiniteDimensional F N] :
    ∃ N' : IntermediateField F L, N ≤ N' ∧ FiniteDimensional F N' ∧ IsGalois F N' := by
  classical
  set B := Module.finBasis F N
  set f : Polynomial F := ∏ i, minpoly F (B i : L)
  have hint : ∀ i, IsIntegral F (B i : L) := fun i =>
    (IsIntegral.of_finite F (B i)).map (IntermediateField.val N)
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => minpoly.ne_zero (hint i)
  set N' := IntermediateField.adjoin F (f.rootSet L)
  have hsplit : (f.map (algebraMap F L)).Splits := IsAlgClosed.splits _
  have : Polynomial.IsSplittingField F N' f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hfin : FiniteDimensional F N' := Polynomial.IsSplittingField.finiteDimensional N' f
  have : Normal F N' := Normal.of_isSplittingField f
  have : IsGalois F N' := IsGalois.mk
  refine ⟨N', ?_, hfin, this⟩
  have hB : ∀ i, (B i : L) ∈ N' := fun i => by
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hf0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_finsetProd]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval F (B i : L))
  intro x hx
  have := congrArg (fun u : N => (u : L)) (B.sum_repr ⟨x, hx⟩)
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this
  rw [← this]
  exact N'.sum_mem fun i _ => N'.smul_mem (hB i)

section InC

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C] [IsAlgClosed C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p

variable [IsPerfectoidField C p]

theorem exists_eq_untiltField (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ M : IntermediateField K♭ C♭, FiniteDimensional K♭ M ∧ untiltField K C p M = L := by
  obtain ⟨N, hN, hLN⟩ := exists_le_untiltField (p := p) L
  have : PerfectField K♭ := PerfectRing.toPerfectField K♭ p
  obtain ⟨N', hNN', hN', hgal⟩ := exists_isGalois_le N
  obtain ⟨M, -, hM, hML⟩ :=
    exists_untiltField_eq_of_le N' L (hLN.trans (untiltField_mono hNN'))
  exact ⟨M, hM, hML⟩

instance isPerfectoidField_of_finiteDimensional (L : IntermediateField K C) [FiniteDimensional K L] :
    IsPerfectoidField L p := by
  obtain ⟨M, hM, hML⟩ := exists_eq_untiltField (p := p) L
  exact IsPerfectoidField.of_ringEquiv p (IntermediateField.equivOfEq hML).toRingEquiv
    fun _ => rfl

end InC

end GroundTheory.PAdicHodge
