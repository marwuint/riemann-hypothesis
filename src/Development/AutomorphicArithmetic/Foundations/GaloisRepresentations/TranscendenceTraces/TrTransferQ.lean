import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.EtaleCohomology.EtaleTrace.LTransferCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Gal.TranscendenceTraces

def TrPushQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) [IsFinite h]
  [IsFinite p] (w : Wt Z), IsWt (h ≫ p) w → IsUnit (l : Γ(S, ⊤)) →
  trHQ l (h ≫ p) w n i ∘ₗ pullHQ l (sch.map h) n i = trHQ l p (w.push h) n i

open LateralTheory.EtaleTrace.Tr (Splits LSpl LLoc LTau)

end UpperTheory.Gal.TranscendenceTraces

end
