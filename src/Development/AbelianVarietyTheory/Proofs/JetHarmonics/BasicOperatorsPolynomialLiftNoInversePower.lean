import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPolyDiffOpRadialPartEqShiftedOperator
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MirrorTodaRadialOperatorPolynomialCoefficientLif
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyLiftConjLastMinorMulRadialPairTerm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialLiftDualOperatorCombination

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem mem_nfSpan_zero_zero_one_of_mem {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {P : M.Par}
    (d : Q.NFData P A) (T : Set A) {x : A} (hx : x ∈ T) : x ∈ nfSpan d T 0 0 1 := by
  refine Submodule.subset_span ⟨1, (bmon d).one_mem, [x], rfl, ?_, ?_⟩
  · intro h hh
    rw [List.mem_singleton] at hh
    exact hh ▸ hx
  · simp

theorem basicLiftAll_zero : BasicLiftAll (fun _ => 0) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN x hx
  obtain ⟨y, -, h | h | h | h⟩ := hx
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ _root_.GlobalTheory.HatNF.polyLift_ahat Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ _root_.GlobalTheory.MirrorToda.polyLift_ahatv Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ _root_.GlobalTheory.HatNF.LiftR.polyLift_rh Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ _root_.GlobalTheory.HatNF.MirrorLift.polyLift_rhv Wp Wq P Bs X μ L st l0 d hD hN y)

end GlobalTheory.HatNF
